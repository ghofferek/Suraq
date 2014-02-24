/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */
package at.iaik.suraq.resProof;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.parser.LogicParser;
import at.iaik.suraq.parser.VeriTParser;
import at.iaik.suraq.proof.VeriTToken;
import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtsolver.VeriTSolver;
import at.iaik.suraq.util.ImmutableSet;
import at.iaik.suraq.util.Util;

public class ResProof {

    // public static final int MAX_PROOF_SIZE = 100000;
    // public static final int MAX_LIT_NUM = 10000;

    /* Essential fields */// GHnote: Whatever that is supposed to mean.

    /**
     * The root node
     */
    private final ResNode root;

    /**
     * the next fresh id.
     */
    private int freshId = 1;

    // public int[] varPart = new int[ResProof.MAX_LIT_NUM];
    /**
     * Map from literal IDs to partitions.
     */
    private final Map<Integer, Integer> varPart = new HashMap<Integer, Integer>();

    // public boolean[] visited = new boolean[ResProof.MAX_PROOF_SIZE];
    /**
     * Helper set to check which nodes were already visited during recursive
     * operations.
     */
    private final Set<Integer> visited = new HashSet<Integer>();

    /* Proof vital */// GHnote: Whatever that is supposed to mean.

    /**
     * Stores whether the vital information on this proof is fresh.
     */
    private boolean vitalInfoFresh = false;

    // public ResNode[] nodeRef = new ResNode[ResProof.MAX_PROOF_SIZE];
    /**
     * Map from IDs to all nodes.
     */
    private final Map<Integer, ResNode> nodeRef = new HashMap<Integer, ResNode>();

    /**
     * Probably the number of nodes. Not sure yet.
     */
    private int numberOfNodes;

    /**
     * Counting nodes being dumped or loaded
     */
    private int dumpLoadCounter = 0;

    /**
     * Probably the set of all leaves. Not sure yet.
     */
    private final HashSet<ResNode> leaves = new HashSet<ResNode>();

    /**
     * Maps clause identifiers from veriT to already created ResNodes. Will be
     * destroyed after parsing is complete!
     */
    private Map<String, ResNode> namesOfResNodes = new HashMap<String, ResNode>();

    /**
     * 
     * Constructs a new <code>ResProof</code>.
     */
    public ResProof() {
        root = new ResNode(0);
    }

    /**
     * Constructs a new <code>ResProof</code>.
     * 
     * @param proof
     * @param replacements
     * @param literalIds
     *            map from (canonic) strings to literal IDs
     * @param literalMap
     *            map from literal IDs (Integers) to <code>Formula</code>
     *            objects
     * 
     * @param leafPartitions
     *            "output parameter" for partitions of leaf nodes
     * @throws IOException
     */
    public static ResProof create(Set<VeritProofNode> leaves,
            Map<VeritProofNode, VeritProofNode> replacements,
            Map<Integer, Formula> literalMap, LogicParser logicParser)
            throws IOException {

        assert (leaves != null);
        assert (replacements != null);

        Map<String, Integer> literalIds = new HashMap<String, Integer>();
        Map<ImmutableSet<Integer>, Integer> leafPartitions = new HashMap<ImmutableSet<Integer>, Integer>();
        Map<Integer, Integer> partitions = new HashMap<Integer, Integer>();
        ResProof resProof = new ResProof();
        String fileNamePrefix = SuraqOptions.getInstance()
                .getInputWithoutExtension();
        BufferedReader stream = null;
        int maxLit = 0;
        if (SuraqOptions.getInstance().getUseThisPropProofFile() == null) {
            File tmpDimacsFile = File.createTempFile("tmp", ".dimacs",
                    new File("./"));
            BufferedWriter writer = new BufferedWriter(new FileWriter(
                    tmpDimacsFile));

            Set<VeritProofNode> allLeaves = new HashSet<VeritProofNode>(leaves);
            for (VeritProofNode node : replacements.keySet()) {
                allLeaves.remove(node);
                VeritProofNode replacement = replacements.get(node);
                assert (replacement != null);
                Set<VeritProofNode> replacementLeaves = replacement.getLeaves();
                allLeaves.addAll(replacementLeaves);
            }

            for (VeritProofNode leaf : allLeaves) {
                Set<Integer> clause = new HashSet<Integer>(leaf
                        .getLiteralConclusions().size());
                for (Formula literal : leaf.getLiteralConclusions()) {
                    int literalId = Util.getLiteralId(literal, literalIds,
                            partitions, literalMap);
                    if (Util.isNegativeLiteral(literal))
                        literalId *= -1;
                    writer.write(Integer.toString(literalId));
                    writer.write(' ');
                    clause.add(literalId);
                }
                writer.write("0\n");
                int leafPartition;
                if (!leaves.contains(leaf) || leaf.isAxiom()) {
                    // This is a leaf in the subproof of a replacement node
                    Set<Integer> tmpPartitions = leaf
                            .getPartitionsFromSymbols();
                    tmpPartitions.remove(-1);
                    assert (tmpPartitions.size() <= 1);
                    leafPartition = tmpPartitions.isEmpty() ? 0 : tmpPartitions
                            .iterator().next();
                } else {
                    leafPartition = leaf.getLeafPartition();
                }
                leafPartitions.put(ImmutableSet.create(clause), leafPartition);
            }
            writer.close();

            Util.dumpMetaData(fileNamePrefix, literalIds, literalMap,
                    partitions, leafPartitions);

            VeriTSolver solver = new VeriTSolver();
            solver.solveDimacs(tmpDimacsFile);
            assert (solver.getState() == VeriTSolver.UNSAT);
            stream = solver.getStream();
            maxLit = literalIds.size();

        } else {
            assert (logicParser != null);
            stream = new BufferedReader(new FileReader(SuraqOptions
                    .getInstance().getUseThisPropProofFile()));
            try {
                literalMap.clear();
                literalMap.putAll(Util.loadLiteralMap(fileNamePrefix
                        + ".literalMap", logicParser));
            } catch (ParseError exc) {
                Util.printToSystemOutWithWallClockTimePrefix("Parse Error: "
                        + exc.getMessage() == null ? exc.getMessage() : "");
                stream.close();
                throw new RuntimeException(exc);
            }
            partitions = Util.loadPartitions(fileNamePrefix + ".partitions");
            leafPartitions = Util.loadLeafPartitions(fileNamePrefix
                    + ".leafPartitions");

            for (Integer lit : literalMap.keySet()) {
                if (lit > maxLit)
                    maxLit = lit;
            }
        }
        assert (maxLit != 0);
        assert (stream != null);
        VeriTParser parser = new VeriTParser(stream, maxLit, resProof,
                partitions, leafPartitions);
        parser.parse();
        stream.close();
        resProof.killNamesOfResNodes();

        return resProof;
    }

    private void killNamesOfResNodes() {
        this.namesOfResNodes = null;
    }

    /**
     * part for axioms should be 0
     * 
     * @param clause
     * @param part
     * @return
     */
    public ResNode addLeaf(Clause cl, int part) {
        assert (!vitalInfoFresh);
        ResNode n = new ResNode(freshId++, cl, null, null, 0, part);
        nodeRef.put(n.id, n);
        return n;
    }

    /**
     * Adds a leaf with the given id.
     * 
     * @param cl
     * @param part
     * @param id
     * @return
     */
    public ResNode addLeaf(Clause cl, int part, int id) {
        freshId = freshId > id ? freshId : id + 1;
        ResNode n = new ResNode(id, cl, null, null, 0, part);
        nodeRef.put(n.id, n);
        return n;
    }

    /**
     * if clause==null then the clause is computed by applying resolution on
     * left and right. If pivot == 0 then pivot variable is also discovered
     * automatically. Node: part for internal node is set to be -1.
     */
    public ResNode addIntNode(Clause cl, ResNode left, ResNode right, int pivot) {
        assert (!vitalInfoFresh);
        ResNode n = new ResNode(freshId++, cl, left, right, pivot, -1);
        nodeRef.put(n.id, n);
        return n;
    }

    /**
     * Adds an internal node with the given id.
     * 
     * @param cl
     * @param left
     * @param right
     * @param pivot
     * @return
     */
    public ResNode addIntNode(Clause cl, ResNode left, ResNode right,
            int pivot, int id) {
        assert (!vitalInfoFresh);
        freshId = freshId > id ? freshId : id + 1;
        ResNode n = new ResNode(id, cl, left, right, pivot, -1);
        nodeRef.put(n.id, n);
        return n;
    }

    public void setRoot(ResNode n) {
        assert (!vitalInfoFresh);
        assert (n.getClause().isEmpty());
        // GHnote: Not sure what this is supposed to do
        root.setLeft(n);
        n.addParent(root);
    }

    /**
     * @return the root of the proof.
     */
    public ResNode getRoot() {

        // GHnote: Not sure why this is done this way.
        // see also: setRoot(ResNode n)
        return root.getLeft();
    }

    /**
     * Destroys the vital information
     */
    private void disruptVitals() {
        vitalInfoFresh = false;
        nodeRef.clear();
        numberOfNodes = 0;
        leaves.clear();
    }

    /**
     * Internal recursion for computation of vital information.
     * 
     * @param n
     */
    private void recComputeVitals(ResNode n) {
        if (visited.contains(n.id))
            return;
        numberOfNodes++;
        nodeRef.put(n.id, n);
        if (n.isLeaf()) {
            leaves.add(n);
        } else {
            recComputeVitals(n.getLeft());
            recComputeVitals(n.getRight());
        }
        visited.add(n.id);
    }

    /**
     * Computes the vital information.
     */
    protected void computeVitals() {
        disruptVitals();
        visited.clear();
        ResNode root = getRoot();
        if (root != null)
            recComputeVitals(root);
        vitalInfoFresh = true;
    }

    /**
     * Internal recursion for dumping the proof.
     * 
     * @param wr
     * @param n
     * @throws IOException
     */
    private void recDumpProof(BufferedWriter wr, ResNode n) throws IOException {
        if (visited.contains(n.id))
            return;
        dumpLoadCounter++;
        if (n.isLeaf()) {
            wr.write(String.valueOf(n.id));
            wr.write(" ");
            wr.write(String.valueOf(n.getPivot()));
            wr.write(" ");
            wr.write(String.valueOf(n.getPart()));
            wr.write(" ");
            Iterator<Literal> iter = n.getClause().iterator();
            while (iter.hasNext()) {
                Literal l = iter.next();
                wr.write(String.valueOf(l.getLit()));
                wr.write(" ");
            }
        } else {
            recDumpProof(wr, n.getLeft());
            recDumpProof(wr, n.getRight());
            wr.write(String.valueOf(n.id));
            wr.write(" ");
            wr.write(String.valueOf(n.getPivot()));
            wr.write(" ");
            wr.write(String.valueOf(n.getLeft().id));
            wr.write(" ");
            wr.write(String.valueOf(n.getRight().id));
            wr.write(" ");
        }
        wr.write("\n");
        visited.add(n.id);
    }

    /**
     * Dumps the proof to the file with the given name.
     * 
     * @param file
     */
    public void dumpProof(String file) {
        // String file = "tmp/test.res";
        visited.clear();
        dumpLoadCounter = 0;
        try {
            // create FileOutputStream object
            File fl = new File(file);
            FileWriter fs = new FileWriter(fl);
            BufferedWriter wr = new BufferedWriter(fs);
            for (int v : varPart.keySet()) {
                wr.write(String.valueOf(v));
                wr.write(" ");
                wr.write(String.valueOf(varPart.get(v)));
                wr.write("\n");
            }
            wr.write(String.valueOf(0));
            wr.write("\n");
            recDumpProof(wr, getRoot());
            wr.write(String.valueOf(0));
            wr.write("\n");
            // int v = 123;
            // wr.write(String.valueOf(v));
            wr.close();

        } catch (IOException e) {
            System.out.println("IOException : " + e);
        }
        Util.printToSystemOutWithWallClockTimePrefix("Dump counter: "
                + Util.largeNumberFormatter.format(dumpLoadCounter));
    }

    /**
     * Loads the proof from the file with the given name.
     * 
     * @param file
     * @return the proof parsed from <code>file</code>
     */
    public static ResProof loadProof(String file) {
        ResProof resProof = new ResProof();
        resProof.dumpLoadCounter = 0;
        try {
            // create FileOutputStream object
            File fl = new File(file);
            FileReader fs = new FileReader(fl);
            BufferedReader rd = new BufferedReader(fs);

            String rdLine;

            while ((rdLine = rd.readLine()) != null) {
                String[] is = rdLine.split(" ");
                int v = Integer.parseInt(is[0]);
                if (v == 0)
                    break;
                // "var and only parts should be there"
                assert (is.length == 2);
                resProof.varPart.put(v, Integer.parseInt(is[1]));
            }
            ResNode n = null;
            while ((rdLine = rd.readLine()) != null) {
                String[] is = rdLine.split(" ");
                int id = Integer.parseInt(is[0]);
                if (id == 0)
                    break;
                int piv = Integer.parseInt(is[1]);
                if (piv == 0) {
                    int part = Integer.parseInt(is[2]);
                    List<Literal> clLits = new ArrayList<Literal>();
                    for (int i = 3; i < is.length; i++) {
                        Literal l = Literal.create(Integer.parseInt(is[i]));
                        clLits.add(l);
                    }
                    Clause cl = new Clause(clLits);
                    n = resProof.addLeaf(cl, part, id);
                    resProof.dumpLoadCounter++;
                } else {
                    int lid = Integer.parseInt(is[2]);
                    int rid = Integer.parseInt(is[3]);
                    n = resProof.addIntNode(null, resProof.nodeRef.get(lid),
                            resProof.nodeRef.get(rid), piv, id);
                    resProof.dumpLoadCounter++;
                }
            }
            resProof.setRoot(n);
            rd.close();
        } catch (IOException e) {
            System.out.println("IOException : " + e);
        }
        Util.printToSystemOutWithWallClockTimePrefix("Load counter: "
                + Util.largeNumberFormatter.format(resProof.dumpLoadCounter));
        return resProof;
    }

    /**
     * Internal recursion for checking the proof.
     * 
     * @param node
     * @param doPrint
     *            print info while checking (not recommended for large proofs)
     */
    private boolean recCheckProof(ResNode node, boolean doPrint) {
        if (visited.contains(node.id))
            return true;
        visited.add(node.id);
        if (doPrint)
            System.out.println(node);
        if (node.isLeaf()) {
            if (node.getPivot() != 0)
                // "Pivot at leaf!",
                return false;
            if (node.getLeft() != null || node.getRight() != null)
                // "Parent of a leaf!",
                return false;
            Iterator<Literal> iter = node.getClause().iterator();
            while (iter.hasNext()) {
                Literal lit = iter.next();
                if (!varPart.containsKey(lit.id()))
                    // "a local with uninitialized partition",
                    return false;
                if (varPart.get(lit.id()) != 0)
                    if (varPart.get(lit.id()) != node.getPart())
                        // "a local is in wrong partition!",
                        return false;
            }
        } else {
            if (node.getLeft() == null || node.getRight() == null)
                // "A parent missing!",
                return false;
            if (!node.getLeft().getClause().contains(node.getPivot(), true)
                    || !node.getRight().getClause()
                            .contains(node.getPivot(), false))
                // "pivot literals are not present in parents!",
                return false;
            Clause clause = new Clause(node.getLeft().getClause(), node
                    .getRight().getClause(), node.getPivot());
            if (!node.getClause().equals(clause))
                // "node is not the result of resolution of parents",
                return false;
            boolean checkLeft = recCheckProof(node.getLeft(), doPrint);
            if (!checkLeft)
                return false;
            boolean checkRight = recCheckProof(node.getRight(), doPrint);
            if (!checkRight)
                return false;
        }
        return true;
    }

    /**
     * Checks the proof.
     * 
     * @param doPrint
     * @return
     */
    public boolean checkProof(boolean doPrint) {
        if (doPrint) {
            System.out.println("============== Checking Proof ============");
            if (vitalInfoFresh) {
                System.out.println("Number of nodes  = " + numberOfNodes);
                System.out.println("Number of leaves = " + leaves.size());
            } else {
                System.out.println("Number of active nodes unknown.");
            }
            System.out.print("var partitions:");
            for (Integer v : varPart.keySet())
                System.out.print(" " + v + ":p" + varPart.get(v));
            System.out.println("\n==========================================");
        }
        visited.clear();
        boolean result = true;
        ResNode root = getRoot();
        if (root != null) {
            // Assert.assertTrue("Root is not empty clause", root.cl.isEmpty());
            if (!root.getClause().isEmpty())
                return false;
            result = recCheckProof(root, doPrint);
            System.out.println("Checked "
                    + Util.largeNumberFormatter.format(visited.size())
                    + " nodes.");
        }
        if (doPrint)
            System.out.println("==========================================");
        return result;
    }

    /**
     * Internal recursion of rmDoubleLits.
     * 
     * @param node
     */
    private void recRmDoubleLits(ResNode node) {
        if (visited.contains(node.id))
            return;
        if (node.isLeaf()) {
            visited.add(node.id);
            return;
        }

        recRmDoubleLits(node.getLeft());
        recRmDoubleLits(node.getRight());
        visited.add(node.id);
        // Node may get removed in refresh
        if (!node.refresh())
            return;

        if (node.getClause().contains(node.getPivot(), true)) {
            node.moveParents(true);
        } else if (node.getClause().contains(node.getPivot(), false)) {
            node.moveParents(false);
        }
    }

    /**
     * Probably removes double literals from clauses. (And thus obsolete nodes
     * from the proof.)
     */
    public void rmDoubleLits() {
        disruptVitals();
        visited.clear();
        recRmDoubleLits(getRoot());
    }

    private void reOrderStep(ResNode node) {
        boolean move = false;
        do {
            // If a node is derived form both parents
            // that are "local" or "global axiom"
            // then convert the node into a local node by
            // setting n.part
            //
            // n.part == 0 -> axiom or only derived from axioms
            // n.part == -1 -> derived from clauses of different parts
            // n.part > 0 -> derived from a single part or global axioms
            int leftPart = node.getLeft().getPart();
            int rightPart = node.getRight().getPart();
            if (leftPart != -1
                    && rightPart != -1
                    && (leftPart == rightPart || leftPart == 0 || rightPart == 0)) {
                int nodePart = 0;
                if (leftPart == 0)
                    nodePart = rightPart;
                else
                    nodePart = leftPart;
                node.setPart(nodePart);
                return;
            }
            // if pivot is global then return
            assert (varPart.containsKey(node.getPivot()));
            if (varPart.get(node.getPivot()) == 0)
                return;

            // Check and fix if child pivot is in n
            move = false;
            boolean leftChild = false;
            boolean leftGrandChild = false;
            // Note: the following condition only checks the partition.
            // If the child is derived from a single partition then
            // we will not move in the direction and don't worry about it.
            if (node.getLeft().getPart() == -1) {
                if (node.getClause().contains(node.getLeft().getPivot(), true)) {
                    move = true;
                    leftChild = true;
                    leftGrandChild = true;
                } else if (node.getClause().contains(node.getLeft().getPivot(),
                        false)) {
                    move = true;
                    leftChild = true;
                    leftGrandChild = false;
                }
            }

            if (!move && node.getRight().getPart() == -1) {
                if (node.getClause().contains(node.getRight().getPivot(), true)) {
                    move = true;
                    leftChild = false;
                    leftGrandChild = true;
                } else if (node.getClause().contains(
                        node.getRight().getPivot(), false)) {
                    move = true;
                    leftChild = false;
                    leftGrandChild = false;
                }
            }

            if (move) {
                node.moveChild(leftChild, leftGrandChild);
                if (!node.refresh())
                    return;
            }
        } while (move);

        // move up the local resolution
        Literal posPivot = Literal.create(node.getPivot(), true);
        Literal negPivot = Literal.create(node.getPivot(), false);
        // Check Left
        int goLeft = node.getLeft().checkMovable(posPivot);
        // Check Right
        int goRight = node.getRight().checkMovable(negPivot);
        // System.out.println("Moving a node!"+n);

        assert (goLeft != -1 || goRight != -1);// n +
                                               // ":Both unmovable parents is not possible!",

        // L = Res(LL, LR), R = Res(RL, RR), N = Res(L,R)
        ResNode L = node.getLeft();
        ResNode R = node.getRight();
        ResNode n1 = null;
        ResNode n2 = null;
        ResNode LL = null;
        ResNode LR = null;
        ResNode RL = null;
        ResNode RR = null;
        int piv = node.getPivot();
        int Lpiv = 0;
        int Rpiv = 0;
        if (L.getPart() == -1) {
            LL = L.getLeft();
            LR = L.getRight();
            Lpiv = L.getPivot();
        }
        if (R.getPart() == -1) {
            RL = R.getLeft();
            RR = R.getRight();
            Rpiv = R.getPivot();
        }

        if (goLeft == 2) { // -> N1 = Res(LL,R) N = Res(N1,LR)
            assert (LL != null);
            assert (R != null);
            n1 = addIntNode(null, LL, R, piv);
            node.setLeft(n1);
            node.setRight(LR);
            node.setPivot(Lpiv);
        } else if (goLeft == 3) { // -> N1 = Res(LR,R) N = Res(LL,N1)
            assert (LR != null);
            assert (R != null);
            n1 = addIntNode(null, LR, R, piv);
            node.setLeft(LL);
            node.setRight(n1);
            node.setPivot(Lpiv);
        } else if (goRight == 2) { // -> N1 = Res(L,RL) N = Res(N1,RR)
            assert (L != null);
            assert (RL != null);
            n1 = addIntNode(null, L, RL, piv);
            node.setLeft(n1);
            node.setRight(RR);
            node.setPivot(Rpiv);
        } else if (goRight == 3) { // -> N1 = Res(L,RR) N = Res(RL,N1)
            assert (L != null);
            assert (RR != null);
            n1 = addIntNode(null, L, RR, piv);
            node.setLeft(RL);
            node.setRight(n1);
            node.setPivot(Rpiv);
        } else if (goLeft == 1) {// -> N1=Res(LL,R) N2=Res(LR,R) N = Res(N1,N2)
            assert (LL != null);
            assert (R != null);
            assert (LR != null);
            n1 = addIntNode(null, LL, R, piv);
            n2 = addIntNode(null, LR, R, piv);
            node.setLeft(n1);
            node.setRight(n2);
            node.setPivot(Lpiv);
        } else if (goRight == 1) {// -> N1=Res(L,RL) N2=Res(L,RR) N = Res(N1,N2)
            assert (L != null);
            assert (RL != null);
            assert (RR != null);
            n1 = addIntNode(null, L, RL, piv);
            n2 = addIntNode(null, L, RR, piv);
            node.setLeft(n1);
            node.setRight(n2);
            node.setPivot(Rpiv);
        }
        node.getLeft().addParent(node);
        node.getRight().addParent(node);
        L.rmParentWithCleanUp(node);
        R.rmParentWithCleanUp(node);

        reOrderStep(n1);
        if (n2 != null)
            reOrderStep(n2);

        if (!node.refresh())
            return;

    }

    /**
     * Internal recursion of deLocalize.
     * 
     * @param node
     */
    private void recDeLocalizeProof(ResNode node) {
        if (visited.contains(node.id))
            return;
        if (node.isLeaf() || node.getPart() != -1) {
            visited.add(node.id);
            if (visited.size() % 10000 == 0) {
                Util.printToSystemOutWithWallClockTimePrefix("Visited "
                        + Util.largeNumberFormatter.format(visited.size())
                        + " nodes.");
            }
            return;
        }
        recDeLocalizeProof(node.getLeft());
        recDeLocalizeProof(node.getRight());
        visited.add(node.id);
        if (visited.size() % 10000 == 0) {
            Util.printToSystemOutWithWallClockTimePrefix("Visited "
                    + Util.largeNumberFormatter.format(visited.size())
                    + " nodes.");
        }

        // Node may get removed in refresh
        if (!node.refresh())
            return;

        reOrderStep(node);
    }

    /**
     * deLocalize the proof.
     */
    public void deLocalizeProof() {
        disruptVitals();
        visited.clear();
        recDeLocalizeProof(getRoot());
    }

    /**
     * Does rmDoubleLits followed by deLocalizeProof. Optionally verifies,
     * prints and dumps the proof.
     * 
     * @param verify
     * @param print
     * @param dump
     * 
     * @return <code>iff</code> verification was enabled and failed.
     */
    public boolean makeLocalFirst(boolean verify, boolean print, boolean dump) {

        HashSet<ResNode> oldLeaves = null;
        if (verify) {
            Util.printToSystemOutWithWallClockTimePrefix("      Computing vitals ...");
            computeVitals();
            Util.printToSystemOutWithWallClockTimePrefix("      Done.");
            Util.printToSystemOutWithWallClockTimePrefix("      Checking ResProof ...");
            if (!checkProof(print))
                return false;
            Util.printToSystemOutWithWallClockTimePrefix("      Done.");
            oldLeaves = new HashSet<ResNode>(leaves);
        }
        if (dump)
            dumpProof("tmp/test.res");
        Util.printToSystemOutWithWallClockTimePrefix("      rmDoubleLits ...");
        rmDoubleLits();
        Util.printToSystemOutWithWallClockTimePrefix("      Done.");
        if (verify) {
            Util.printToSystemOutWithWallClockTimePrefix("      Checking ResProof...");
            if (!checkProof(print))
                return false;
            Util.printToSystemOutWithWallClockTimePrefix("      Done.");
        }
        Util.printToSystemOutWithWallClockTimePrefix("      deLocalize ...");
        deLocalizeProof();
        Util.printToSystemOutWithWallClockTimePrefix("      Done.");
        if (verify) {
            Util.printToSystemOutWithWallClockTimePrefix("      Computing vitals ...");
            computeVitals();
            Util.printToSystemOutWithWallClockTimePrefix("      Done.");
            Util.printToSystemOutWithWallClockTimePrefix("      Checking ResProof.");
            if (!checkProof(print))
                return false;
            Util.printToSystemOutWithWallClockTimePrefix("      Done.");
            if (!oldLeaves.containsAll(leaves))
                return false;
        }
        return true;
    }

    /**
     * Stores the given partition for the given variable. Fails if the
     * variable's partition has been set already.
     * 
     * @param var
     * @param part
     */
    public void putVarPart(int var, int part) {
        assert (!varPart.containsKey(var));
        varPart.put(var, part);
    }

    /**
     * 
     * @return size of the proof.
     */
    public int size() {
        if (vitalInfoFresh)
            return numberOfNodes;
        computeVitals();
        return numberOfNodes;
    }

    /**
     * 
     * @return the size of the proof when unwinding the DAG.
     */
    public long treeSize() {
        Map<ResNode, Long> nodeSizes = new HashMap<ResNode, Long>();
        return this.getRoot().treeSize(nodeSizes);
    }

    /**
     * @param name
     * @param type
     * @param conclusions
     * @param parsed_clauses
     * @param partitionsMap
     *            a map from literal IDs to partitions (0 being global)
     */
    public void add(String name, Token type, List<Formula> conclusions,
            String[] parsed_clauses, Map<Integer, Integer> partitionsMap,
            Map<ImmutableSet<Integer>, Integer> leafPartitions) {
        if (type.equals(VeriTToken.INPUT)) {
            // We ignore INPUT-nodes with OR-formulas as conclusions
            if (conclusions.size() == 1) {
                if (conclusions.get(0) instanceof OrFormula)
                    return;
            }
        }

        if (type.equals(VeriTToken.OR) || type.equals(VeriTToken.INPUT)) {
            // This is a leaf

            List<Literal> resClauseLits = new ArrayList<Literal>();
            Set<Integer> resClausePartitions = new HashSet<Integer>();

            for (Formula literal : conclusions) {
                // assign literal IDs
                Formula posLiteral = Util.makeLiteralPositive(literal);
                assert (Util.isLiteral(posLiteral));
                assert (Util.isAtom(posLiteral));
                if (posLiteral.equals(PropositionalConstant.create(false))) {
                    resClausePartitions.add(0); // resProof package uses "0" for
                                                // globals
                    continue;
                }
                assert (posLiteral instanceof PropositionalVariable);
                Integer resLiteralID = Integer
                        .valueOf(((PropositionalVariable) posLiteral)
                                .getVarName().substring(2));
                int partition = partitionsMap.get(resLiteralID);
                this.varPart.put(resLiteralID, partition);
                resClauseLits.add(Literal.create(resLiteralID,
                        Util.getSignValue(literal)));
                resClausePartitions.add(partition < 0 ? 0 : partition);
            }

            // build leaf ResNodes

            if (resClausePartitions.size() == 2)
                resClausePartitions.remove(0); // resProof package uses "0"
                                               // for globals
            assert (resClausePartitions.size() == 1);
            int leafPartition = resClausePartitions.iterator().next();
            if (leafPartition == 0) {
                Set<Integer> tmpClause = new TreeSet<Integer>();
                for (Literal lit : resClauseLits) {
                    tmpClause.add(lit.signed_var());
                }
                ImmutableSet<Integer> clause = ImmutableSet.create(tmpClause);
                assert (leafPartitions.containsKey(clause));
                assert (leafPartitions.get(clause) >= 0);
                leafPartition = leafPartitions.get(clause);
            }
            Clause clause = new Clause(resClauseLits);
            ResNode resLeafNode = this.addLeaf(clause, leafPartition);
            assert (resLeafNode != null);
            namesOfResNodes.put(name, resLeafNode);
            return;
        }

        // ------------------------------------------------------------------------------------------
        if (type.equals(VeriTToken.RESOLUTION)) {
            // This is an internal node

            List<ResNode> remainingNodes = new LinkedList<ResNode>();
            if (parsed_clauses.length > 2) {

                for (String clause : parsed_clauses) {
                    ResNode node = namesOfResNodes.get(clause);
                    assert (node != null);
                    remainingNodes.add(node);
                }
                while (true) {
                    assert (remainingNodes.size() > 2);
                    ResNode left = remainingNodes.remove(0);
                    ResNode right = remainingNodes.remove(0);
                    ResNode intermediateNode = this.addIntNode(null, left,
                            right, 0);
                    remainingNodes.add(0, intermediateNode);
                    if (remainingNodes.size() == 2)
                        break;
                }
            } else {
                ResNode left = namesOfResNodes.get(parsed_clauses[0]);
                ResNode right = namesOfResNodes.get(parsed_clauses[1]);
                assert (left != null);
                assert (right != null);
                remainingNodes.add(left);
                remainingNodes.add(right);
            }
            assert (remainingNodes.size() == 2);

            // build literal of resolution

            ResNode resIntNode = this.addIntNode(null, remainingNodes.get(0),
                    remainingNodes.get(1), 0);
            namesOfResNodes.put(name, resIntNode);
            assert (resIntNode != null);
            if (resIntNode.getClause().isEmpty())
                this.setRoot(resIntNode);
            return;
        }

        // Unknown node type
        assert (false);
    }

}