/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.ObjectStreamException;
import java.io.Serializable;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.resProof.Clause;
import at.iaik.suraq.resProof.Literal;
import at.iaik.suraq.resProof.ResNode;
import at.iaik.suraq.resProof.ResProof;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.TransformedZ3Proof;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.util.HashTagContainer;
import at.iaik.suraq.util.ImmutableSet;
import at.iaik.suraq.util.MutableInteger;
import at.iaik.suraq.util.SplitterBookkeeper;
import at.iaik.suraq.util.Timer;
import at.iaik.suraq.util.UncolorableLeafSplitter;
import at.iaik.suraq.util.Util;

/**
 * This Proof consists of several VeritProofNodes. You shall not try to modify
 * the parents/childs of these VeritProofNodes on your own. Use this class to
 * add/remove ProofNodes(=ProofSets)
 * 
 * @author chillebold
 * 
 */

public class VeritProof implements Serializable {

    private static final long serialVersionUID = 1L;

    /**
     * Used for debugging purposes during interpolation.
     */
    Map<Integer, Formula> partitions = null;

    /**
     * Map from proof node names (e.g. ".c44") to nodes.
     */
    private final HashMap<String, VeritProofNode> proofNodes = new HashMap<String, VeritProofNode>();

    /**
     * The root of the proof. Can only be set once.
     */
    private VeritProofNode root = null;

    /**
     * Counts how many clauses have been added to this proof. Provides unique
     * numbers for new clauses.
     */
    private int clauseCounter = 0;

    /**
     * Maps leafs of the proof to their partitions. For real leafs, this is
     * computed based on symbols. For pseudo-leafs (and, or), it is based on the
     * partition of the corresponding real leaf.
     */
    private final Map<VeritProofNode, Integer> partitionsOfLeafs = new HashMap<VeritProofNode, Integer>();

    /**
     * This field can be used to quickly turn off checks of proofs (but not
     * necessarily proof nodes, if they are called independently).
     */
    private static boolean checkProofEnabled = true;

    /**
     * Used to make node names fresh.
     */
    private long freshNodeNumber = 1;

    /**
     * Stores names that have been reserved as fresh names, and are currently
     * being processed to be added to the proof. This allows higher
     * parallelization as we do not need to make the entire processing of a
     * fresh new proof node atomic. We just (atomically) reserve a name, process
     * the new node in parallel, and then add it (atomically).
     */
    private final Set<String> reservedNames = new HashSet<String>();

    /**
     * Returns a (new) <code>VeritProofNode</code>. It is automatically attached
     * to its clauses (as a Parent). Then the generated VeritProofNode is
     * returned.
     * 
     * @param prefix
     *            the prefix for the fresh node name
     * @param suffix
     *            the suffix for the fresh node name
     * @param type
     *            type of the Node (e.g. VeriTToken.EQ_TRANSITIVE,...)
     * @param conclusions
     *            a list of Formulas
     * @param clauses
     *            a list of VeritProofNodes that are the clauses(=parents) of
     *            the currently added
     * @param iargs
     *            a freshNodeNumber as an Integer (e.g. 1)
     * 
     * @param removeSubproofsOfTheoryLemmas
     *            specifies whether or not subproofs of theory lemmas should be
     *            discarded
     * 
     * @return the requested proof node.
     */
    public VeritProofNode addProofNodeWithFreshName(String prefix,
            String suffix, Token type, List<Formula> conclusions,
            List<VeritProofNode> clauses, Integer iargs,
            boolean removeSubproofsOfTheoryLemmas) {
        VeritProofNode result = addProofNode(
                this.freshNodeName(prefix, suffix), type, conclusions, clauses,
                iargs, removeSubproofsOfTheoryLemmas);
        return result;
    }

    /**
     * Returns a (new) <code>VeritProofNode</code>. It is automatically attached
     * to its clauses (as a Parent). Then the generated VeritProofNode is
     * returned.
     * 
     * @param name
     *            name of the Node (e.g. ".c22")
     * @param type
     *            type of the Node (e.g. VeriTToken.EQ_TRANSITIVE,...)
     * @param conclusions
     *            a list of Formulas
     * @param clauses
     *            a list of VeritProofNodes that are the clauses(=parents) of
     *            the currently added
     * @param iargs
     *            a freshNodeNumber as an Integer (e.g. 1)
     * 
     * @param removeSubproofsOfTheoryLemmas
     *            specifies whether or not subproofs of theory lemmas should be
     *            discarded
     * 
     * @return the requested proof node.
     */
    public VeritProofNode addProofNode(String name, Token type,
            List<Formula> conclusions, List<VeritProofNode> clauses,
            Integer iargs, boolean removeSubproofsOfTheoryLemmas) {

        assert (conclusions != null);

        if (proofNodes.keySet().contains(name))
            throw new RuntimeException("Name of proof node is not unique.");

        VeritProofNode node = null;

        int partition = -38317; // Magic freshNodeNumber, easy to find when it
                                // turns up
                                // somewhere accidentally
        if (type.equals(VeriTToken.INPUT)) {
            // This is a "real" input node.
            // Compute its partition based on symbols and store it.
            Set<Integer> partitions = new HashSet<Integer>();
            for (Formula conclusion : conclusions) {
                partitions.addAll(conclusion.getPartitionsFromSymbols());
            }
            assert (partitions.size() <= 2);
            partitions.remove(-1);
            assert (partitions.size() <= 1);
            if (partitions.isEmpty()) {
                // This could happen if there are no noDependenceVars
                // in the spec. This corner case is not handled yet.
                throw new RuntimeException(
                        "Unable to determine partition of leaf node in proof due to missing noDependenceVars. This corner case is not handled yet.;");
            }
            assert (partitions.size() == 1);
            partition = partitions.iterator().next();
            assert (partition > 0);
        }
        if (type.equals(VeriTToken.AND) || type.equals(VeriTToken.OR)) {
            // This is a "pseudo-" leaf. Compute its partition
            // based on its child before forgetting about the child.
            assert (clauses.size() == 1);
            synchronized (this) {
                assert (partitionsOfLeafs.containsKey(clauses.get(0)));
                assert (partitionsOfLeafs.get(clauses.get(0)) > 0);
                partition = partitionsOfLeafs.get(clauses.get(0));
            }
            type = VeriTToken.INPUT;
            clauses = new ArrayList<VeritProofNode>();
            iargs = null;
        }

        node = new VeritProofNode(name, type, conclusions, clauses, iargs,
                this, removeSubproofsOfTheoryLemmas);
        assert (node != null);

        assert (node != null);
        if (partition > 0) {
            synchronized (this) {
                partitionsOfLeafs.put(node, partition);
            }
        }

        // Check whether this is the root node
        if (conclusions.size() == 0) {
            synchronized (this) {
                assert (this.root == null);
                this.root = node;
            }
        }

        return node;
    }

    /**
     * Adds the given node to this proof. The node must already claim to belong
     * to this proof. This method is intended for adding intermediate nodes that
     * are created during addition of another node. (I.e., nodes that split
     * multi-resolution in single resolutions.
     * 
     * @param node
     */
    protected synchronized void addProofNode(VeritProofNode node) {
        assert (node.getProof() == this);
        addNodeToInternalDataStructures(node);
    }

    /**
     * Adds the given node to the internal data structures (cache, etc.).
     * 
     * @param node
     */
    private synchronized void addNodeToInternalDataStructures(
            VeritProofNode node) {
        if (proofNodes.get(node.getName()) != null) {
            throw new RuntimeException("Duplicate node name: " + node.getName());
        }
        this.clauseCounter++;
        String name = node.getName();
        proofNodes.put(name, node);
        reservedNames.remove(name);
    }

    /**
     * get the freshNodeNumber of literal Conclusions in all VeriTProofNodes
     * attached to this VeritProof
     * 
     * @return the freshNodeNumber of literal Conclusions in all VeriTProofNodes
     *         attached to this VeritProof
     */
    public int getLiteralConclusionsCount() {
        int size = 0;
        for (VeritProofNode proofSet : proofNodes.values()) {
            List<Formula> litConclusions = proofSet.getLiteralConclusions();
            if (litConclusions != null)
                size += litConclusions.size();
        }
        return size;
    }

    /**
     * removes a proofSet in the VeritProof. It is detached from all its parents
     * and from all its parents.
     * 
     * @param proofNode
     */
    @SuppressWarnings("deprecation")
    @Deprecated
    public void removeProofSet(VeritProofNode proofNode) {
        if (proofNode.getParents() != null)
            for (VeritProofNode parent : proofNode.getParents())
                parent.removeSubProof(proofNode);
        if (proofNode.getSubProofs() != null)
            for (VeritProofNode subproof : proofNode.getSubProofs())
                subproof.removeParent(proofNode);

        proofNodes.remove(proofNode.getName());
    }

    /**
     * Removes a (parentless) node from this proof. If its subproofs have no
     * other parents, they will be removed as well.
     * 
     * @param node
     *            the (parentless) node to remove.
     */
    protected void removeDanglingProofNode(VeritProofNode node) {
        assert (node.getParents().isEmpty());
        proofNodes.remove(node.getName());

        for (VeritProofNode child : node.getSubProofs()) {
            child.removeParent(node);
            if (child.getParents().isEmpty())
                removeDanglingProofNode(child);
        }

    }

    /**
     * returns the VeritProofNode defined by a given name (e.g. ".c99")
     * 
     * @param name
     *            the name of a VeritProofNode (e.g ".c99")
     * @return the VeritProofNode
     */
    public VeritProofNode getProofNode(String name) {
        VeritProofNode node = proofNodes.get(name);
        assert (node != null);
        return node;
    }

    /**
     * Returns a non-Mutable HashSet of ProofSets
     * 
     * @return an immutable set of all nodes of this proof
     */
    public ImmutableSet<VeritProofNode> getProofNodes() {
        return ImmutableSet.create(proofNodes.values());
    }

    /**
     * prints the content of this VeritProof in Verit-Format as readed into a
     * String.
     * 
     * @return the Verit-Format of this VeritProof
     */
    @Override
    public String toString() {
        StringBuilder str = new StringBuilder();
        for (VeritProofNode proof : getProofNodes())
            str = str.append(proof.toString() + "\n");
        return str.toString();
    }

    /**
     * @return <code>true</code> if this proof does not contain bad literals
     */
    public boolean hasNoBadLiterals() {
        for (VeritProofNode node : proofNodes.values()) {
            for (Formula literal : node.getLiteralConclusions()) {
                assert (Util.isLiteral(literal));
                if (Util.isBadLiteral(literal))
                    return false;
            }
        }
        return true;
    }

    /**
     * Performs the following checks on this proof:
     * <ul>
     * <li>Each node is a correct deduction</li>
     * <li>The parent-child-relations match</li>
     * <li>All nodes claim to belong to this proof</li>
     * <li>All nodes in the cache and the goodDefinitionOfBadLiterals are also
     * in the proofNodes</li>
     * <li>The root is not <code>null</code>, and belongs to the proofNodes</li>
     * <li>The root has no parents</li>
     * <li>All nodes, except the root, have at least one parent</li>
     * <li>For each node in the proofNodes, there is a node with the same
     * conclusion in the nodeCache</li>
     * </ul>
     * Easy checks are performed first (early fail strategy).
     * 
     * @return <code>true</code> if this proof checks out correct.
     */
    public boolean checkProof() {

        if (!VeritProof.checkProofEnabled) {
            Util.printToSystemOutWithWallClockTimePrefix("[INFO] A check of the proof was requested, but proof checking is disabled.");
            return true;
        }

        Util.printToSystemOutWithWallClockTimePrefix("[INFO] Starting a complete proof check...");
        Util.printToSystemOutWithWallClockTimePrefix("[INFO] Size of proof: "
                + Util.largeNumberFormatter.format(this.size()));
        Timer timer = new Timer();
        timer.start();

        if (root == null)
            return false;
        if (!root.getParents().isEmpty())
            return false;
        if (proofNodes.get(root.getName()) != root)
            return false;
        if (!root.getLiteralConclusions().isEmpty())
            return false;

        Util.printToSystemOutWithWallClockTimePrefix("[INFO] Now performing checks on individual nodes...");
        int done = 0;
        int lastReported = 0;
        for (VeritProofNode node : proofNodes.values()) {
            int percentage = (int) Math.floor(((double) done++ / proofNodes
                    .size()) * 100);
            if (percentage >= lastReported + 10) {
                lastReported += 10;
                Util.printToSystemOutWithWallClockTimePrefix("  " + percentage
                        + "% done.");
            }
            if (node.getType().equals(VeriTToken.AND)
                    || node.getType().equals(VeriTToken.OR))
                // AND and OR should not occur in "real" proofs.
                // They are removed during/after parsing.
                return false;

            for (VeritProofNode child : node.getSubProofs()) {
                if (!child.getParents().contains(node))
                    return false;
            }
            for (VeritProofNode parent : node.getParents()) {
                if (!parent.getSubProofs().contains(node))
                    return false;
            }

            if (node.getProof() != this)
                return false;

            if (node != root) {
                if (node.getParents().isEmpty())
                    return false;
            }

            if (!node.checkProofNode())
                return false;
        }
        Util.printToSystemOutWithWallClockTimePrefix("  All checks on individual nodes done.");

        if (!this.isAcyclic())
            return false;

        // All checks passed
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("[INFO] Complete proof check done. All tests passed. Time required: "
                + timer);
        return true;
    }

    /**
     * 
     * @return the <code>root</code> of this proof. (Can be <code>null</code>,
     *         if it was not set yet.)
     */
    public VeritProofNode getRoot() {
        return root;
    }

    /**
     * Sets the given root as the new root, if it has no parents and proofs
     * false.
     * 
     * @param newRoot
     * @return <code>true</code> if the new root was set
     */
    protected boolean setNewRoot(VeritProofNode newRoot) {
        if (newRoot.getLiteralConclusions().size() > 0)
            return false;
        if (newRoot.getParents().size() > 0)
            return false;
        root = newRoot;
        return true;
    }

    /**
     * Removes all nodes which are not reachable from the root. If the root is
     * <code>null</code>, nothing is done.
     */
    public void removeUnreachableNodes() {
        if (root == null)
            return;

        Set<VeritProofNode> reachableNodes = getReachableNodes();
        Set<VeritProofNode> unreachableNodes = new HashSet<VeritProofNode>(
                proofNodes.values());
        unreachableNodes.removeAll(reachableNodes);

        Set<VeritProofNode> parentlessUnreachableNodes = new HashSet<VeritProofNode>();

        for (VeritProofNode unreachableNode : unreachableNodes) {
            // Sanity check
            assert (unreachableNode != root);
            assert (unreachableNode != null);
            for (VeritProofNode parent : unreachableNode.getParents()) {
                if (reachableNodes.contains(parent))
                    throw new RuntimeException(
                            "Unreachable node has reachable parent. This should not happen.");
                if (!unreachableNodes.contains(parent))
                    throw new RuntimeException(
                            "Unreachable node has non-unreachable parent. This should not happen.");
            }
            if (unreachableNode.getParents().isEmpty())
                parentlessUnreachableNodes.add(unreachableNode);
        }
        for (VeritProofNode node : parentlessUnreachableNodes)
            this.removeDanglingProofNode(node);

        // Done. Just some final assertions.
        assert (proofNodes.size() == reachableNodes.size());
        assert ((new HashSet<VeritProofNode>(proofNodes.values()))
                .equals(reachableNodes));
    }

    /**
     * 
     * @return the set of nodes reachable from <code>root</code>, or
     *         <code>null</code> if <code>root</code> is <code>null</code>.
     */
    protected Set<VeritProofNode> getReachableNodes() {
        if (root == null)
            return null;

        Set<VeritProofNode> result = new HashSet<VeritProofNode>();
        result.add(root);
        for (VeritProofNode child : root.getSubProofs())
            getReachableNodes(result, child);

        return result;
    }

    /**
     * @param result
     * @param child
     */
    private void getReachableNodes(Set<VeritProofNode> result,
            VeritProofNode node) {
        for (VeritProofNode child : node.getSubProofs()) {
            if (!result.contains(child))
                getReachableNodes(result, child);
        }
        result.add(node);
    }

    /**
     * Splits leaves into colorable subproofs.
     * 
     * @return a <code>Map</code> from originals to replacements.
     */
    public Map<VeritProofNode, VeritProofNode> splitUncolorableLeaves() {

        Set<VeritProofNode> leafs = this.getLeaves();
        Util.printToSystemOutWithWallClockTimePrefix("Found " + leafs.size()
                + " leafs.");
        Set<VeritProofNode> leavesToClean = new HashSet<VeritProofNode>();

        for (VeritProofNode leaf : leafs) {
            Set<Integer> partitions = leaf.getPartitionsFromSymbols();
            partitions.remove(-1);
            if (partitions.size() > 1) {
                assert (leaf.isAxiom());
                leavesToClean.add(leaf);
            }
        }

        Util.printToSystemOutWithWallClockTimePrefix("  "
                + leavesToClean.size() + " need splitting.");

        final int numThreads = SuraqOptions.getInstance()
                .getNumSplitterThreads();
        assert (numThreads > 0);
        Util.printToSystemOutWithWallClockTimePrefix("Creating " + numThreads
                + " splitter threads.");

        // Last thread takes the "remainder" of the division
        final int numNodesPerThread = leavesToClean.size() / numThreads == 0 ? 1
                : leavesToClean.size() / numThreads;
        UncolorableLeafSplitter[] splitters = new UncolorableLeafSplitter[numThreads];
        Iterator<VeritProofNode> nodeIterator = leavesToClean.iterator();
        for (int id = 0; id < numThreads; id++) {
            List<VeritProofNode> leavesForThisSplitter = new ArrayList<VeritProofNode>(
                    numNodesPerThread);
            if (id < numThreads - 1) {
                for (int numNodes = 0; numNodes < numNodesPerThread; numNodes++) {
                    leavesForThisSplitter.add(nodeIterator.next());
                }
            } else {
                while (nodeIterator.hasNext())
                    leavesForThisSplitter.add(nodeIterator.next());
            }
            UncolorableLeafSplitter splitter = new UncolorableLeafSplitter(id,
                    leavesForThisSplitter, Thread.currentThread());
            splitters[id] = splitter;
        }

        ThreadMXBean tmxb = ManagementFactory.getThreadMXBean();
        try {
            tmxb.setThreadCpuTimeEnabled(true);
            tmxb.setThreadContentionMonitoringEnabled(true);
        } catch (Exception exc1) {
            System.out.println("Could not enable thread time monitoring.");
        }
        Timer timer = new Timer();
        timer.start();
        Thread[] threads = new Thread[numThreads];
        List<Long> threadIds = new ArrayList<Long>(numThreads);
        for (int id = 0; id < numThreads; id++) {
            Thread thread = new Thread(splitters[id], "Splitter_" + id);
            threads[id] = thread;
            threadIds.add(thread.getId());
            thread.start();
        }
        // Now all threads are running
        SplitterBookkeeper bookkeeper = new SplitterBookkeeper(splitters,
                threadIds, timer);
        Thread bookkeeperThread = new Thread(bookkeeper);
        bookkeeperThread.start();
        for (int id = 0; id < numThreads; id++) {
            try {
                threads[id].join();
            } catch (InterruptedException exc) {
                Util.printToSystemOutWithWallClockTimePrefix("InterruptedException while waiting for splitters.");
                throw new RuntimeException(exc);
            }
        }
        timer.stop();
        bookkeeper.kill();
        bookkeeperThread.interrupt();
        try {
            bookkeeperThread.join();
        } catch (InterruptedException exc) {
            Util.printToSystemOutWithWallClockTimePrefix("InterruptedException while waiting for bookkeeper.");
        }
        Util.printToSystemOutWithWallClockTimePrefix("All splitters done");
        // Now all threads are done. Collect results.
        int totalLiteralsFewer = 0;
        int numStrongerClauses = 0;
        Map<VeritProofNode, VeritProofNode> replacements = new HashMap<VeritProofNode, VeritProofNode>();
        for (UncolorableLeafSplitter splitter : splitters) {
            assert (splitter.isAllOk());
            totalLiteralsFewer += splitter.getTotalLiteralsFewer();
            numStrongerClauses += splitter.getNumStrongerClauses();
            replacements.putAll(splitter.getReplacements());
        }
        Util.printToSystemOutWithWallClockTimePrefix("Total literals saved: "
                + totalLiteralsFewer);
        Util.printToSystemOutWithWallClockTimePrefix("Number of clauses made stronger:"
                + numStrongerClauses);
        Util.printToSystemOutWithWallClockTimePrefix("Num replacements: "
                + replacements.size());
        assert (replacements.size() == leavesToClean.size());
        assert (replacements.keySet().containsAll(leavesToClean));

        return replacements;
        // -------------------------------------------------------------
        // Util.printToSystemOutWithWallClockTimePrefix("Now replacing uncolorable leaves with colorable subproofs.");
        //
        // int count = 0;
        // for (VeritProofNode leafToClean : replacements.keySet()) {
        // VeritProofNode replacement = replacements.get(leafToClean);
        // assert (replacement != null);
        // Util.printToSystemOutWithWallClockTimePrefix("  Replacing leaf "
        // + leafToClean.getName() + " with subproof of size "
        // + replacement.getReachableNodes().size());
        // assert (leafToClean.getLiteralConclusions().containsAll(replacement
        // .getLiteralConclusions()));
        //
        // Set<VeritProofNode> parentsCopy = new HashSet<VeritProofNode>(
        // leafToClean.getParents());
        // int numNodesUpdated = 0;
        // for (VeritProofNode parent : parentsCopy) {
        // if (!leafToClean.getParents().contains(parent))
        // continue;
        // numNodesUpdated += parent
        // .makeStronger(leafToClean, replacement);
        // }
        // Util.printToSystemOutWithWallClockTimePrefix("    Done " + ++count
        // + " (Approx. " + numNodesUpdated + " nodes updated)");
        // }
        // Util.printToSystemOutWithWallClockTimePrefix("  All done.");
        // Util.printToSystemOutWithWallClockTimePrefix("Now removing unreachable nodes.");
        // Util.printToSystemOutWithWallClockTimePrefix("Size before: "
        // + this.size());
        // this.removeUnreachableNodes();
        // Util.printToSystemOutWithWallClockTimePrefix("Size after: "
        // + this.size());
        // assert (this.isColorable());
        // assert (this.checkProof());
        //
        // if (leavesToClean.size() > 0) {
        // String path = null;
        // SuraqOptions options = SuraqOptions.getInstance();
        // if (options.getUseThisProofFile() != null) {
        // path = options.getUseThisProofFile();
        // if (path.endsWith(".smt2")) {
        // path = new String(path.subSequence(0, path.length() - 5)
        // + "_split.smt2");
        // } else
        // path = path + "_split.smt2";
        // } else {
        // path = options.getInput();
        // if (path.endsWith(".smt2")) {
        // path = new String(path.subSequence(0, path.length() - 6)
        // + "_proof_split.smt2");
        // } else
        // path = path + "_proof_split.smt2";
        // }
        // File file = new File(path);
        // try {
        // BufferedWriter writer = new BufferedWriter(new FileWriter(file));
        // Util.printToSystemOutWithWallClockTimePrefix("Now writing proof to file "
        // + file.toString());
        // this.writeOut(writer);
        // writer.close();
        // } catch (IOException exc) {
        // Util.printToSystemOutWithWallClockTimePrefix("IOException while trying to write proof to file. Details follow.");
        // Util.printToSystemOutWithWallClockTimePrefix(exc.getMessage() == null
        // ? "(no message)"
        // : exc.getMessage());
        // exc.printStackTrace();
        // }
        // }
        //
    }

    /**
     * @return <code>true</code> all leafs of this proof are colorable.
     */
    public boolean isColorable() {
        for (VeritProofNode node : proofNodes.values()) {
            if (!node.isLeaf())
                continue;
            else {
                Set<Integer> partitions = node.getPartitionsFromSymbols();
                partitions.remove(-1);
                if (partitions.size() > 1)
                    return false;
            }
        }
        return true;
    }

    /**
     * Sanity check for illegal cycles in the DAG. If the root is not set, this
     * method returns <code>true</code>.
     * 
     * @return <code>true</code> if the proof contains cycles (reachable from
     *         the root).
     */
    public boolean isAcyclic() {
        Timer timer = new Timer();
        timer.start();
        Util.printToSystemOutWithWallClockTimePrefix("Starting check for acyclicity.");

        if (root == null) {
            Util.printToSystemOutWithWallClockTimePrefix("Root is null. Check was trivial.");
            return true;
        }
        List<VeritProofNode> path = new ArrayList<VeritProofNode>();
        Set<VeritProofNode> notPartOfCycle = new HashSet<VeritProofNode>();

        boolean result = root.isAcyclic(path, notPartOfCycle,
                new MutableInteger(0));
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("Finished check for acyclicity. Took "
                + timer);
        return result;
    }

    /**
     * This method iterates over the <code>proofNode</code> HashMap. This is
     * fast but comes at the price of returning some potentially unreachable
     * leaves as well. Remove unreachable nodes before calling this method to
     * avoid the problem.
     * 
     * An alternative is the method {@link VeritProofNode#getLeaves()}.
     * 
     * @return all leaves of this proof.
     */
    public Set<VeritProofNode> getLeaves() {
        Set<VeritProofNode> result = new HashSet<VeritProofNode>();
        for (VeritProofNode node : proofNodes.values()) {
            if (node.isLeaf())
                result.add(node);
        }
        return result;
    }

    /**
     * Rewrites the proof to get rid of the given bad literal definition.
     * 
     * @param currentLeaf
     *            a good definition of a bad literal
     */
    @SuppressWarnings({ "unused", "deprecation" })
    @Deprecated
    private void cleanProof(VeritProofNode currentLeaf) {
        assert (currentLeaf.isLeaf());
        assert (currentLeaf.isGoodDefinitionOfBadLiteral());

        Formula badLiteral = currentLeaf.getDefinedBadLiteral();
        assert (badLiteral != null);
        Formula inverseBadLiteral = Util.invertLiteral(badLiteral);
        List<Formula> definingLiterals = currentLeaf.getDefiningGoodLiterals();
        assert (definingLiterals != null);

        Map<Formula, VeritProofNode> resolvedLiterals = new HashMap<Formula, VeritProofNode>();

        // Search for resolution of bad literal
        VeritProofNode currentNode = currentLeaf;
        VeritProofNode previousNode = null;
        while (!currentNode.resolvesOn(badLiteral)) {
            assert (!currentNode.getParents().isEmpty());

            // Record which literals are resolved along the path
            if (previousNode != null) {
                Formula resolvingLiteral = currentNode.findResolvingLiteral();
                if (!previousNode.getLiteralConclusionsAsSet().contains(
                        resolvingLiteral)) {
                    resolvingLiteral = Util.invertLiteral(resolvingLiteral);
                    assert (previousNode.getLiteralConclusionsAsSet()
                            .contains(resolvingLiteral));
                }
                resolvedLiterals
                        .put(Util.makeLiteralPositive(resolvingLiteral),
                                currentNode
                                        .getChildWithLiteralInOppositePolarity(resolvingLiteral));
            }
            previousNode = currentNode;
            currentNode = currentNode.getParents().iterator().next();
        }
        VeritProofNode turningPoint = currentNode;

        // Replace inverse bad literal in other subtree
        Map<VeritProofNode, VeritProofNode> dagOperationCache = new HashMap<VeritProofNode, VeritProofNode>();
        VeritProofNode otherChild = turningPoint
                .getChildWithLiteralInOppositePolarity(badLiteral);
        assert (otherChild.getLiteralConclusions().contains(inverseBadLiteral));
        VeritProofNode updatedTurningPointChild = otherChild
                .replaceInverseBadLiteral(inverseBadLiteral, definingLiterals,
                        dagOperationCache);
        //
        // // OLD CODE
        // // Go back up the other way, record the path
        // Stack<VeritProofNode> path = new Stack<VeritProofNode>();
        // path.push(currentNode);
        // while (!currentNode.getSubProofs().isEmpty()) {
        // boolean found = false;
        // for (VeritProofNode currentChild : currentNode.getSubProofs()) {
        // if (currentChild.getLiteralConclusionsAsSet().contains(
        // inverseBadLiteral)) {
        // // Currently, we cannot handle the case that both subproofs
        // // contain the inverse bad literal
        // assert (!found);
        // currentNode = currentChild;
        // path.push(currentNode);
        // found = true;
        // }
        // }
        // assert (found);
        // }
        // assert (currentNode.getSubProofs().isEmpty());
        //
        // // Replace nodes on the path
        // VeritProofNode oldPreviousNode = null;
        // VeritProofNode newPreviousNode = null;
        // currentNode = path.pop();
        // while (true) {
        // List<Formula> newConclusion = new ArrayList<Formula>();
        // for (Formula literal : currentNode.getLiteralConclusions()) {
        // if (literal.equals(inverseBadLiteral))
        // newConclusion.addAll(definingLiterals);
        // else
        // newConclusion.add(literal);
        // }
        //
        // List<VeritProofNode> newClauses = new ArrayList<VeritProofNode>();
        // for (VeritProofNode node : currentNode.getSubProofs()) {
        // if (node == oldPreviousNode) {
        // assert (newPreviousNode != null);
        // newClauses.add(newPreviousNode);
        // } else
        // newClauses.add(node);
        // }
        //
        // // check node cache for an existing node
        // VeritProofNode newNode = null;
        // WeakReference<VeritProofNode> reference = nodeCache
        // .get(ImmutableSet.create(newConclusion));
        // if (reference != null) {
        // newNode = reference.get();
        // if (newNode != null) {
        // // Check whether its a node on the path. If so, do not take
        // // it.
        // if (path.contains(newNode) || newNode.equals(turningPoint))
        // newNode = null;
        // }
        // }
        //
        // if (newNode == null) {
        // newNode = new VeritProofNode("repl" + currentNode.getName(),
        // currentNode.getType(), newConclusion, newClauses,
        // currentNode.getIargs(), this);
        // nodeCache.put(ImmutableSet.create(newConclusion),
        // new WeakReference<VeritProofNode>(newNode));
        // }
        //
        // // update variables
        // newPreviousNode = newNode;
        // oldPreviousNode = currentNode;
        // if (path.isEmpty())
        // break;
        // else
        // currentNode = path.pop();
        // }
        //
        // assert (currentNode == turningPoint);
        // currentNode = newPreviousNode;

        // Resolve literals that should already have been resolved before the
        // turning point
        currentNode = updatedTurningPointChild;
        while (true) {
            Set<Formula> literalsToResolve = new HashSet<Formula>();
            literalsToResolve.addAll(currentNode.getLiteralConclusionsAsSet());
            literalsToResolve.removeAll(turningPoint
                    .getLiteralConclusionsAsSet());
            if (literalsToResolve.isEmpty())
                break;

            Formula literalToResolve = literalsToResolve.iterator().next();
            assert (resolvedLiterals.containsKey(Util
                    .makeLiteralPositive(literalToResolve)));

            List<Formula> newConclusion = new ArrayList<Formula>();
            newConclusion.addAll(currentNode.getLiteralConclusions());
            newConclusion.addAll(resolvedLiterals.get(
                    Util.makeLiteralPositive(literalToResolve))
                    .getLiteralConclusionsAsSet());
            newConclusion.remove(literalsToResolve);
            newConclusion.remove(Util.invertLiteral(literalToResolve));

            List<VeritProofNode> newClauses = new ArrayList<VeritProofNode>(2);
            newClauses.add(resolvedLiterals.get(Util
                    .makeLiteralPositive(literalToResolve)));
            newClauses.add(currentNode);

            VeritProofNode newNode = null;

            // WeakReference<VeritProofNode> reference = nodeCache
            // .get(ImmutableSet.create(newConclusion));
            // if (reference != null) {
            // newNode = reference.get();
            // if (newNode != null) {
            // // Check whether its a node on the path. If so, do not take
            // // it.
            // if (path.contains(newNode) || newNode.equals(turningPoint))
            // newNode = null;
            // }
            // }
            if (newNode == null) {
                newNode = new VeritProofNode(this.freshNodeName("res.", ""),
                        VeriTToken.RESOLUTION, newConclusion, newClauses, null,
                        this, false);
            }
            currentNode = newNode;
        }

        // Update parents of turning point
        assert (turningPoint.getLiteralConclusionsAsSet().equals(currentNode
                .getLiteralConclusionsAsSet()));
        for (VeritProofNode parent : turningPoint.getParents()) {
            turningPoint.removeParent(parent);
            assert (!turningPoint.getParents().contains(parent));
            boolean updated = parent.updateProofNode(turningPoint, currentNode);
            assert (!parent.getSubProofs().contains(turningPoint));
            assert (updated);
        }
    }

    /**
     * Reorders the resolutions steps in this proof so that locals come first.
     * 
     * @return the recovered proof, after reordering
     */
    public TransformedZ3Proof reorderResolutionSteps() {
        ResProof resProof = new ResProof();

        Map<String, Integer> literalsID = new HashMap<String, Integer>();
        Map<VeritProofNode, ResNode> resNodes = new HashMap<VeritProofNode, ResNode>();
        Map<Integer, Formula> literalMap = new HashMap<Integer, Formula>();

        ResNode rootNode = createResProofRecursive(this.root, resProof,
                literalsID, literalMap, resNodes);
        resProof.setRoot(rootNode);

        resProof.checkProof(false);
        resProof.rmDoubleLits();
        resProof.deLocalizeProof();
        resProof.checkProof(false);

        Map<ResNode, TransformedZ3Proof> cache = new HashMap<ResNode, TransformedZ3Proof>();
        TransformedZ3Proof recoveredProof = new TransformedZ3Proof(
                resProof.getRoot(), literalMap, cache);

        return recoveredProof;
    }

    /**
     * @param node
     *            the node to convert
     * @param resProof
     * @param literalsID
     * @param literalMap
     * @param resNodes
     * @return the <code>ResNode</code> corresponding to the given
     *         <code>node</code>.
     */
    private ResNode createResProofRecursive(VeritProofNode node,
            ResProof resProof, Map<String, Integer> literalsID,
            Map<Integer, Formula> literalMap,
            Map<VeritProofNode, ResNode> resNodes) {
        assert (node != null);
        assert (resProof != null);
        assert (literalsID != null);
        assert (literalMap != null);
        assert (resNodes != null);

        ResNode result = resNodes.get(node);
        if (result != null)
            return result;

        Token proofType = node.getType();

        if (proofType.equals(VeriTToken.INPUT) || node.isAxiom()) {

            OrFormula clause = node.getConclusionsAsOrFormula();
            List<Literal> resClauseLits = new ArrayList<Literal>();
            // TODO: check if correct
            Set<Integer> resClausePartitions = new HashSet<Integer>();

            for (Formula literal : clause.getDisjuncts()) {
                // assign literal IDs
                Formula posLiteral = Util.makeLiteralPositive(literal);
                assert (Util.isLiteral(posLiteral));
                assert (Util.isAtom(posLiteral));
                if (posLiteral.equals(PropositionalConstant.create(false))) {
                    resClausePartitions.add(0); // resProof package uses "0" for
                                                // globals
                    continue;
                }
                Integer resLiteralID = literalsID.get(Util
                        .makeIdString(posLiteral));
                Set<Integer> partitions = literal.getPartitionsFromSymbols();
                if (partitions.size() == 2)
                    partitions.remove(-1);
                assert (partitions.size() == 1);
                int partition = partitions.iterator().next();
                assert (partition != 0);
                if (resLiteralID == null) {
                    resLiteralID = literalsID.size() + 1;
                    assert (!literalsID
                            .containsValue(new Integer(resLiteralID)));
                    literalsID.put(Util.makeIdString(posLiteral), resLiteralID);
                    literalMap.put(resLiteralID, posLiteral);
                    resProof.putVarPart(resLiteralID, partition < 0 ? 0
                            : partition);
                }
                resClauseLits.add(Literal.create(resLiteralID,
                        Util.getSignValue(literal)));
                resClausePartitions.add(partition < 0 ? 0 : partition);
            }

            // build leaf ResNodes
            ResNode resLeafNode = resNodes.get(node);
            if (resLeafNode == null) {
                if (resClausePartitions.size() == 2)
                    resClausePartitions.remove(0); // resProof package uses "0"
                                                   // for globals
                assert (resClausePartitions.size() == 1);
                int leafPartition = resClausePartitions.iterator().next();
                if (leafPartition == 0) {
                    if (!node.isAxiom()) { // non-axiom leaf with only globals
                        assert (partitionsOfLeafs.containsKey(node));
                        assert (partitionsOfLeafs.get(node) > 0);
                        leafPartition = partitionsOfLeafs.get(node);
                    }
                }
                Clause tmpClause = new Clause(resClauseLits);
                resLeafNode = resProof.addLeaf(tmpClause, leafPartition);
                resNodes.put(node, resLeafNode);
            }
            assert (resLeafNode != null);
            return resLeafNode;

        } else if (proofType.equals(VeriTToken.RESOLUTION)) {
            assert (node.getSubProofs().size() == 2);
            ResNode resIntNode = resNodes.get(node);
            if (resIntNode == null) {
                assert (node.getSubProofs().size() == 2);
                VeritProofNode child1 = node.getSubProofs().get(0);
                VeritProofNode child2 = node.getSubProofs().get(1);
                ResNode resNode1 = createResProofRecursive(child1, resProof,
                        literalsID, literalMap, resNodes);
                ResNode resNode2 = createResProofRecursive(child2, resProof,
                        literalsID, literalMap, resNodes);
                assert (resNode1 != null);
                assert (resNode2 != null);

                // build literal of resolution
                Formula posLiteral = Util.makeLiteralPositive(node
                        .findResolvingLiteral());
                Integer literalID = literalsID.get(Util
                        .makeIdString(posLiteral));
                assert (literalID != null);
                resIntNode = resProof.addIntNode(null, resNode1, resNode2,
                        literalID);
                resNodes.put(node, resIntNode);
            }
            assert (resIntNode != null);
            return resIntNode;

        } else
            throw new RuntimeException(
                    "Proof should only consist of input and resolution elements");
    }

    /**
     * The clause counter counts how many clauses have been added to this proof.
     * Thus, using this freshNodeNumber in the name of a new node guarantees
     * that it is unique.
     * 
     * @return the clause counter
     */
    public int getClauseCounter() {
        return clauseCounter;
    }

    /**
     * Returns the size of this proof. More precisely, returns the
     * freshNodeNumber of nodes currently stored in the internal map
     * <code>proofNodes</code>.
     * 
     * @return the freshNodeNumber of nodes in this proof.
     */
    public int size() {
        return proofNodes.size();
    }

    /**
     * Returns a node name that does not yet exist in the proof. The name will
     * be of the form <code>prefix + freshNodeNumber + suffix</code>, where
     * freshNodeNumber is either the empty string or the smallest (positive)
     * freshNodeNumber such that the name is fresh.
     * 
     * @param prefix
     * @param suffix
     * @return a node name that does not yet exist in the proof.
     */
    public synchronized String freshNodeName(String prefix, String suffix) {
        assert (prefix != null);
        assert (suffix != null);

        String name = prefix + suffix;
        if (!proofNodes.containsKey(name) && !reservedNames.contains(name)) {
            reservedNames.add(name);
            return name;
        }

        while (freshNodeNumber > 0) {
            name = prefix + freshNodeNumber + suffix;
            if (!proofNodes.containsKey(name) && !reservedNames.contains(name)) {
                reservedNames.add(name);
                return name;
            }
            freshNodeNumber++;
        }
        // No fresh name found
        assert (false);
        return null;
    }

    // Methods for serialization/deserialization

    private void writeObject(java.io.ObjectOutputStream out) throws IOException {
        out.writeObject(proofNodes);
        out.writeObject(root);
        out.writeObject(clauseCounter);

        // Map<String, VeritProofNode> synonymsCopy = new HashMap<String,
        // VeritProofNode>();
        // for (String key : synonyms.keySet()) {
        // WeakReference<VeritProofNode> ref = synonyms.get(key);
        // if (ref != null) {
        // if (ref.get() != null) {
        // synonymsCopy.put(key, ref.get());
        // }
        // }
        // }
        // out.writeObject(synonymsCopy);

        // Map<ImmutableSet<Formula>, VeritProofNode> nodeCacheCopy = new
        // HashMap<ImmutableSet<Formula>, VeritProofNode>();
        // for (ImmutableSet<Formula> key : nodeCache.keySet()) {
        // WeakReference<VeritProofNode> ref = nodeCache.get(key);
        // if (ref != null) {
        // if (ref.get() != null) {
        // nodeCacheCopy.put(key, ref.get());
        // }
        // }
        // }
        // out.writeObject(nodeCacheCopy);

    }

    private void readObject(java.io.ObjectInputStream in) throws IOException,
            ClassNotFoundException {
        try {
            Field proofSetsField = VeritProof.class
                    .getDeclaredField("proofNodes");
            proofSetsField.setAccessible(true);
            proofSetsField.set(this, in.readObject());
            proofSetsField.setAccessible(false);

            root = (VeritProofNode) in.readObject();

            clauseCounter = (Integer) in.readObject();

            // @SuppressWarnings("unchecked")
            // Map<String, VeritProofNode> synonymsCopy = (Map<String,
            // VeritProofNode>) in
            // .readObject();
            // Map<String, WeakReference<VeritProofNode>> synonymsTmp = new
            // HashMap<String, WeakReference<VeritProofNode>>();
            // for (String key : synonymsCopy.keySet()) {
            // if (synonymsCopy.get(key) != null) {
            // synonymsTmp.put(key, new WeakReference<VeritProofNode>(
            // synonymsCopy.get(key)));
            // }
            // }
            // Field synonymsField =
            // VeritProof.class.getDeclaredField("synonyms");
            // synonymsField.setAccessible(true);
            // synonymsField.set(this, synonymsTmp);
            // synonymsField.setAccessible(false);

            // @SuppressWarnings("unchecked")
            // Map<ImmutableSet<Formula>, VeritProofNode> nodeCacheCopy =
            // (Map<ImmutableSet<Formula>, VeritProofNode>) in
            // .readObject();
            // Map<ImmutableSet<Formula>, WeakReference<VeritProofNode>>
            // nodeCacheTmp = new HashMap<ImmutableSet<Formula>,
            // WeakReference<VeritProofNode>>();
            // for (ImmutableSet<Formula> key : nodeCacheCopy.keySet()) {
            // if (nodeCacheCopy.get(key) != null) {
            // nodeCacheTmp.put(key, new WeakReference<VeritProofNode>(
            // nodeCacheCopy.get(key)));
            // }
            // }
            // Field nodeCacheField = VeritProof.class
            // .getDeclaredField("nodeCache");
            // nodeCacheField.setAccessible(true);
            // nodeCacheField.set(this, nodeCacheTmp);
            // nodeCacheField.setAccessible(false);

        } catch (Exception exc) {
            throw new RuntimeException(exc);
        }

    }

    @SuppressWarnings("unused")
    private void readObjectNoData() throws ObjectStreamException {
        throw new RuntimeException(
                "readObjectNoData() was called in VeritProof.");
    }

    /**
     * Writes this proof to the given <code>writer</code>. Only works if
     * <code>root!=null</code>
     * 
     * @param writer
     * @throws IOException
     */
    public void writeOut(BufferedWriter writer) throws IOException {
        if (this.root == null)
            return;
        Set<VeritProofNode> alreadyWritten = new HashSet<VeritProofNode>(
                proofNodes.size());

        HashTagContainer tagContainer = new HashTagContainer();
        root.writeOut(writer, alreadyWritten, tagContainer);
    }

    /**
     * @param <code>checkProofEnabled</code> the new value for
     *        <code>checkProofEnabled</code>
     */
    public static void setCheckProofEnabled(boolean checkProofEnabled) {
        if (checkProofEnabled)
            Util.printToSystemOutWithWallClockTimePrefix("Activating proof checks.");
        else
            Util.printToSystemOutWithWallClockTimePrefix("Deactivating proof checks.");
        VeritProof.checkProofEnabled = checkProofEnabled;
    }

    /**
     * @param node
     * @return
     */
    public Integer getPartitionOfLeaf(VeritProofNode node) {
        assert (node.isLeaf());
        Integer result = partitionsOfLeafs.get(node);
        assert (result != null);
        return result;
    }

    /**
     * Computes an interpolant between even and odd partitions. Since partitions
     * in the symbols and leaf nodes are counted from 1 to 2^n, we will have to
     * subtract 1 every time before we determine whether it's even or odd. That
     * is because the values of control signals iterate from 0 to (2^n)-1. After
     * subtracting 1, even partitions represent "A" (i.e., where the control
     * signal is 0), and odd partitions represent "B" (i.e., where the control
     * signal is 1).
     * 
     * @param partitions
     *            Used only for debugging purposes. Can be null, if assertions
     *            are disabled.
     * 
     * @return an interpolant between the even and the odd partitions of this
     *         proof
     */
    public Formula interpolateEvenVsOddPartitions(
            Map<Integer, Formula> partitions) {
        assert (root != null);
        assert (root.getLiteralConclusions().isEmpty());

        this.partitions = partitions;

        Map<VeritProofNode, Formula> partialInterpolants = new HashMap<VeritProofNode, Formula>(
                Integer.highestOneBit(proofNodes.size() - 1) << 1);
        Formula result = root
                .interpolateEvenVsOddPartitions(partialInterpolants);
        return result;
    }

}
