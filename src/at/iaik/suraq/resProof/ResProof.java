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
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

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

    /* Essential fields */
    public ResNode root = null;
    public int nodeCount = 1;

    // public int[] var_part = new int[ResProof.MAX_LIT_NUM];
    public Map<Integer, Integer> var_part = new HashMap<Integer, Integer>();

    // public boolean[] visited = new boolean[ResProof.MAX_PROOF_SIZE];
    public Set<Integer> visited = new HashSet<Integer>();

    /* Proof vital */
    public boolean vitalInfoFresh = false;

    // public ResNode[] nodeRef = new ResNode[ResProof.MAX_PROOF_SIZE];
    public Map<Integer, ResNode> nodeRef = new HashMap<Integer, ResNode>();

    public int numberOfNodes;
    public HashSet<ResNode> leaves = new HashSet<ResNode>();

    /* config fields */
    public boolean printWhileChecking = false;

    private Map<String, ResNode> namesOfResNodes = new HashMap<String, ResNode>();

    public ResProof() {
        root = new ResNode(0, false);
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
            Map<String, Integer> literalIds, Map<Integer, Formula> literalMap,
            Map<ImmutableSet<Integer>, Integer> leafPartitions)
            throws IOException {

        assert (leaves != null);
        assert (replacements != null);
        assert (literalIds != null);
        assert (literalIds.isEmpty());

        File tmpDimacsFile = File.createTempFile("tmp", ".dimacs", new File(
                "./"));
        BufferedWriter writer = new BufferedWriter(
                new FileWriter(tmpDimacsFile));

        Map<Integer, Integer> partitions = new HashMap<Integer, Integer>();

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
                Set<Integer> tmpPartitions = leaf.getPartitionsFromSymbols();
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

        VeriTSolver solver = new VeriTSolver();
        solver.solveDimacs(tmpDimacsFile);
        assert (solver.getState() == VeriTSolver.UNSAT);

        ResProof resProof = new ResProof();
        VeriTParser parser = new VeriTParser(solver.getStream(),
                literalIds.size(), resProof, partitions, leafPartitions);
        parser.parse();

        return resProof;
    }

    /**
     * part for axioms should be 0
     * 
     * @param cl
     * @param part
     * @return
     */
    public ResNode addLeaf(Collection<Lit> cl, int part) {
        assert (!vitalInfoFresh);
        ResNode n = new ResNode(nodeCount, true, cl, null, null, 0, part);
        incNodeCount(n);
        return n;
    }

    /**
     * if cl==null then the clause is computed by applying resolution on left
     * and right. If pivot == 0 then pivot variable is also discovered
     * automatically. Node: part for internal node is set to be -1.
     */
    public ResNode addIntNode(Collection<Lit> cl, ResNode left, ResNode right,
            int pivot) {
        assert (!vitalInfoFresh);
        ResNode n = new ResNode(nodeCount, false, cl, left, right, pivot, -1);
        incNodeCount(n);
        return n;
    }

    private void incNodeCount(ResNode n) {
        // nodeRef[nodeCount] = n;
        nodeCount++;
        assert (nodeCount < Integer.MAX_VALUE);
    }

    public void setRoot(ResNode n) {
        assert (!vitalInfoFresh);
        root.left = n;
        n.addChild(root);
    }

    public ResNode getRoot() {
        return root.left;
    }

    /*
     * vital computation
     */
    public void disruptVitals() {
        vitalInfoFresh = false;
        nodeRef.clear();
        numberOfNodes = 0;
        leaves.clear();
    }

    public void recComputeVitals(ResNode n) {
        if (visited.contains(n.id))
            return;
        numberOfNodes++;
        nodeRef.put(n.id, n);
        if (n.isLeaf) {
            leaves.add(n);
        } else {
            recComputeVitals(n.left);
            recComputeVitals(n.right);
        }
        visited.add(n.id);
    }

    public void computeVitals() {
        disruptVitals();
        visited.clear();
        ResNode root = getRoot();
        if (root != null)
            recComputeVitals(root);
        vitalInfoFresh = true;
    }

    /*
     * Dumping/loading the proofs in a file
     */
    void recDumpProof(BufferedWriter wr, ResNode n) throws IOException {
        if (visited.contains(n.id))
            return;
        if (n.isLeaf) {
            wr.write(String.valueOf(n.id));
            wr.write(" ");
            wr.write(String.valueOf(n.pivot));
            wr.write(" ");
            wr.write(String.valueOf(n.part));
            wr.write(" ");
            Iterator<Lit> iter = n.cl.iterator();
            while (iter.hasNext()) {
                Lit l = iter.next();
                wr.write(String.valueOf(l.l));
                wr.write(" ");
            }
        } else {
            recDumpProof(wr, n.left);
            recDumpProof(wr, n.right);
            wr.write(String.valueOf(n.id));
            wr.write(" ");
            wr.write(String.valueOf(n.pivot));
            wr.write(" ");
            wr.write(String.valueOf(n.left.id));
            wr.write(" ");
            wr.write(String.valueOf(n.right.id));
            wr.write(" ");
        }
        wr.write("\n");
        visited.add(n.id);
    }

    public void dumpProof(String file) {
        // String file = "tmp/test.res";
        visited.clear();
        try {
            // create FileOutputStream object
            File fl = new File(file);
            FileWriter fs = new FileWriter(fl);
            BufferedWriter wr = new BufferedWriter(fs);
            for (int v = 1; var_part.get(v) != -1; v++) {
                wr.write(String.valueOf(v));
                wr.write(" ");
                wr.write(String.valueOf(var_part.get(v)));
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

    }

    public void loadProof(String file) {
        // String file = "tmp/test.res";
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
                var_part.put(v, Integer.parseInt(is[1]));
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
                    Clause cl = new Clause();
                    for (int i = 3; i < is.length; i++) {
                        Lit l = new Lit(Integer.parseInt(is[i]));
                        cl.addLit(l);
                    }
                    n = addLeaf(cl, part);
                } else {
                    int lid = Integer.parseInt(is[2]);
                    int rid = Integer.parseInt(is[3]);
                    n = addIntNode(null, nodeRef.get(lid), nodeRef.get(rid),
                            piv);
                }
                nodeRef.put(id, n);
            }
            setRoot(n);
            rd.close();
        } catch (IOException e) {
            System.out.println("IOException : " + e);
        }

    }

    /*
     * Checking Proof correctness
     */

    void recCheckProof(ResNode n) {
        if (visited.contains(n.id))
            return;
        if (printWhileChecking)
            System.out.println(n);
        // Todo: Check double lits issue if disabled globally
        if (n.isLeaf) {
            assert (n.pivot == 0); // "Pivot at leaf!",
            assert (n.left == null && n.right == null); // "Parent of a leaf!",
            Iterator<Lit> iter = n.cl.iterator();
            while (iter.hasNext()) {
                Lit l = iter.next();
                assert (var_part.get(l.var()) != -1);// "a local with uninitialized partition",

                if (var_part.get(l.var()) != 0)
                    assert (var_part.get(l.var()) == n.part);// "a local is in wrong partition!",
            }
        } else {
            assert (n.left != null && n.right != null); // "A parent missing!",
            assert (n.left.cl.contains(n.pivot, true) && n.right.cl.contains(
                    n.pivot, false)); // "pivot literals are not present in parents!",
            Clause c = new Clause(n.left.cl, n.right.cl, n.pivot);
            assert (

            n.cl.equals(c)); // "node is not the result of resolution of parents",
            recCheckProof(n.left);
            recCheckProof(n.right);
        }
        visited.add(n.id);
    }

    public void checkProof(boolean doPrint) {
        printWhileChecking = doPrint;
        if (printWhileChecking) {
            System.out.println("============== Checking Proof ============");
            if (vitalInfoFresh) {
                System.out.println("Number of nodes  = " + numberOfNodes);
                System.out.println("Number of leaves = " + leaves.size());
            } else {
                System.out.println("Number of active nodes" + "<" + nodeCount);
            }
            System.out.print("var partitions:");
            for (Integer v : var_part.keySet())
                System.out.print(" " + v + ":p" + var_part.get(v));
            System.out.println("\n==========================================");
        }
        visited.clear();
        ResNode root = getRoot();
        if (root != null) {
            recCheckProof(root);
            // Assert.assertTrue("Root is not empty clause", root.cl.isEmpty());
        }
        if (printWhileChecking)
            System.out.println("==========================================");
    }

    // Start : remove double literals

    void recRmDoubleLits(ResNode n) {
        if (visited.contains(n.id))
            return;
        if (n.isLeaf) {
            visited.add(n.id);
            return;
        }

        recRmDoubleLits(n.left);
        recRmDoubleLits(n.right);
        visited.add(n.id);
        // Node may get removed in refresh
        if (!n.refresh())
            return;

        if (n.cl.contains(n.pivot, true)) {
            n.moveChidren(true);
        } else if (n.cl.contains(n.pivot, false)) {
            n.moveChidren(false);
        }
    }

    public void rmDoubleLits() {
        disruptVitals();
        visited.clear();
        recRmDoubleLits(getRoot());
    }

    // boolean p=false;
    // Start : Proof restructuring-----------------------------------------
    void reOrderStep(ResNode n) {
        // if(n.id==3001) p =true;
        // if(n.id==6432){
        // System.out.println(n);
        // System.out.println(n.left);
        // // System.out.println(n.left.left);
        // // System.out.println(n.left.right);
        // System.out.println(n.right);
        // }
        // if(p) System.out.println(n);

        boolean mv = false;
        do {
            // If a node is derived form both parents
            // that are "local" or "global axiom"
            // then convert the node into a local node by
            // setting n.part
            //
            // n.part == 0 -> axiom or only derived from axioms
            // n.part == -1 -> derived from clauses of different parts
            // n.part > 0 -> derived from a single part or global axioms
            int lp = n.left.part;
            int rp = n.right.part;
            if (lp != -1 && rp != -1 && (lp == rp || lp == 0 || rp == 0)) {
                int np = 0;
                if (lp == 0)
                    np = rp;
                else
                    np = lp;
                n.part = np;
                return;
            }
            // if pivot is global then return
            if (var_part.get(n.pivot) == 0)
                return;

            // Check and fix if parents pivot is in n
            mv = false;
            boolean LeftParent = false, LeftGrandParent = false;
            // Note: the following condition only checks the partition.
            // If the parent is derived from a single partition then
            // we will not move in the direction and dont worry about it.
            if (n.left.part == -1) {
                if (n.cl.contains(n.left.pivot, true)) {
                    mv = true;
                    LeftParent = true;
                    LeftGrandParent = true;
                } else if (n.cl.contains(n.left.pivot, false)) {
                    mv = true;
                    LeftParent = true;
                    LeftGrandParent = false;
                }
            }

            if (!mv && n.right.part == -1) {
                if (n.cl.contains(n.right.pivot, true)) {
                    mv = true;
                    LeftParent = false;
                    LeftGrandParent = true;
                } else if (n.cl.contains(n.right.pivot, false)) {
                    mv = true;
                    LeftParent = false;
                    LeftGrandParent = false;
                }
            }

            if (mv) {
                n.moveParent(LeftParent, LeftGrandParent);
                if (!n.refresh())
                    return;
            }
        } while (mv);

        // move up the local resolution
        Lit pl = new Lit(n.pivot, true);
        Lit nl = new Lit(n.pivot, false);
        // Check Left
        int goLeft = n.left.checkMovable(pl);
        // Check Right
        int goRight = n.right.checkMovable(nl);
        // System.out.println("Moving a node!"+n);

        assert (goLeft != -1 || goRight != -1);// n +
                                               // ":Both unmovable parents is not possible!",

        // L = Res(LL, LR), R = Res(RL, RR), N = Res(L,R)
        ResNode L = n.left, R = n.right, n1 = null, n2 = null;
        ResNode LL = null, LR = null, RL = null, RR = null;
        int piv = n.pivot, Lpiv = 0, Rpiv = 0;
        if (L.part == -1) {
            LL = L.left;
            LR = L.right;
            Lpiv = L.pivot;
        }
        if (R.part == -1) {
            RL = R.left;
            RR = R.right;
            Rpiv = R.pivot;
        }

        if (goLeft == 2) { // -> N1 = Res(LL,R) N = Res(N1,LR)
            n1 = addIntNode(null, LL, R, piv);
            n.left = n1;
            n.right = LR;
            n.pivot = Lpiv;
        } else if (goLeft == 3) { // -> N1 = Res(LR,R) N = Res(LL,N1)
            n1 = addIntNode(null, LR, R, piv);
            n.left = LL;
            n.right = n1;
            n.pivot = Lpiv;
        } else if (goRight == 2) { // -> N1 = Res(L,RL) N = Res(N1,RR)
            n1 = addIntNode(null, L, RL, piv);
            n.left = n1;
            n.right = RR;
            n.pivot = Rpiv;
        } else if (goRight == 3) { // -> N1 = Res(L,RR) N = Res(RL,N1)
            n1 = addIntNode(null, L, RR, piv);
            n.left = RL;
            n.right = n1;
            n.pivot = Rpiv;
        } else if (goLeft == 1) {// -> N1=Res(LL,R) N2=Res(LR,R) N = Res(N1,N2)
            n1 = addIntNode(null, LL, R, piv);
            n2 = addIntNode(null, LR, R, piv);
            n.left = n1;
            n.right = n2;
            n.pivot = Lpiv;
        } else if (goRight == 1) {// -> N1=Res(L,RL) N2=Res(L,RR) N = Res(N1,N2)
            n1 = addIntNode(null, L, RL, piv);
            n2 = addIntNode(null, L, RR, piv);
            n.left = n1;
            n.right = n2;
            n.pivot = Rpiv;
        }
        n.left.addChild(n);
        n.right.addChild(n);
        L.rmChildWithCleanUP(n);
        R.rmChildWithCleanUP(n);

        reOrderStep(n1);
        if (n2 != null)
            reOrderStep(n2);

        if (!n.refresh())
            return;

    }

    void recDeLocalizeProof(ResNode n) {
        if (visited.contains(n.id))
            return;
        if (n.isLeaf || n.part != -1) {
            visited.add(n.id);
            return;
        }
        recDeLocalizeProof(n.left);
        recDeLocalizeProof(n.right);
        visited.add(n.id);

        // Node may get removed in refresh
        if (!n.refresh())
            return;

        reOrderStep(n);
    }

    public void deLocalizeProof() {
        disruptVitals();
        visited.clear();
        recDeLocalizeProof(getRoot());
    }

    public void localFirstProofs(boolean verify, boolean print, boolean dump) {

        HashSet<ResNode> oldLeaves = null;
        if (verify) {
            computeVitals();
            checkProof(print);
            oldLeaves = new HashSet<ResNode>(leaves);
        }
        if (dump)
            dumpProof("tmp/test.res");
        rmDoubleLits();
        deLocalizeProof();
        if (verify) {
            computeVitals();
            checkProof(print);
            assert (oldLeaves.containsAll(leaves));
        }
    }

    public void tranformResProofs() {
        localFirstProofs(false, false, false);
    }

    // End : Proof restructuring-----------------------------------------

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

            List<Lit> resClause = new ArrayList<Lit>();
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
                this.var_part.put(resLiteralID, partition);
                resClause
                        .add(new Lit(resLiteralID, Util.getSignValue(literal)));
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
                for (Lit lit : resClause) {
                    tmpClause.add(lit.signed_var());
                }
                ImmutableSet<Integer> clause = ImmutableSet.create(tmpClause);
                assert (leafPartitions.containsKey(clause));
                assert (leafPartitions.get(clause) >= 0);
                leafPartition = leafPartitions.get(clause);
            }
            ResNode resLeafNode = this.addLeaf(resClause, leafPartition);
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
            if (resIntNode.cl.isEmpty())
                this.setRoot(resIntNode);
            return;
        }

        // Unknown node type
        assert (false);
    }

}