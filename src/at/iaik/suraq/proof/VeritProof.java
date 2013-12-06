/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.io.IOException;
import java.io.ObjectStreamException;
import java.io.Serializable;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.resProof.Lit;
import at.iaik.suraq.resProof.ResNode;
import at.iaik.suraq.resProof.ResProof;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.TransformedZ3Proof;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.util.CongruenceClosure;
import at.iaik.suraq.util.ImmutableSet;
import at.iaik.suraq.util.MutableInteger;
import at.iaik.suraq.util.Timer;
import at.iaik.suraq.util.Util;
import at.iaik.suraq.util.chain.TransitivityCongruenceChain;

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
     * Map from proof node names (e.g. ".c44") to nodes.
     */
    private final HashMap<String, VeritProofNode> proofNodes = new HashMap<String, VeritProofNode>();

    /**
     * The root of the proof. Can only be set once.
     */
    private VeritProofNode root = null;

    /**
     * This stores all <em>leaf</em> nodes where several good literals define a
     * bad literal. E.g. a!=b v b!=c v a=c, for a=c being a bad literal and a=b,
     * b=c being good literals.
     */
    private final HashSet<VeritProofNode> goodDefinitionsOfBadLiterals = new HashSet<VeritProofNode>();

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
    public static boolean checkProofEnabled = true;

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
     *            a list of VeritProofNodes that are the clauses(=children) of
     *            the currently added
     * @param iargs
     *            a number as an Integer (e.g. 1)
     * 
     * @return the requested proof node.
     */
    public VeritProofNode addProofNode(String name, Token type,
            List<Formula> conclusions, List<VeritProofNode> clauses,
            Integer iargs) {

        assert (conclusions != null);

        if (proofNodes.keySet().contains(name))
            throw new RuntimeException("Name of proof node is not unique.");

        VeritProofNode node = null;

        int partition = -38317; // Magic number, easy to find when it turns up
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
            assert (partitionsOfLeafs.containsKey(clauses.get(0)));
            assert (partitionsOfLeafs.get(clauses.get(0)) > 0);
            partition = partitionsOfLeafs.get(clauses.get(0));
            type = VeriTToken.INPUT;
            clauses = new ArrayList<VeritProofNode>();
            iargs = null;
        }

        node = new VeritProofNode(name, type, conclusions, clauses, iargs, this);
        assert (node != null);

        assert (node != null);
        if (partition > 0)
            partitionsOfLeafs.put(node, partition);

        // Check whether this is the root node
        if (conclusions.size() == 0) {
            assert (this.root == null);
            this.root = node;
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
    protected void addProofNode(VeritProofNode node) {
        assert (node.getProof() == this);
        addNodeToInternalDataStructures(node);
    }

    /**
     * Adds the given node to the internal data structures (cache, etc.).
     * 
     * @param node
     */
    private void addNodeToInternalDataStructures(VeritProofNode node) {
        if (proofNodes.get(node.getName()) != null) {
            throw new RuntimeException("Duplicate node name: " + node.getName());
        }
        this.clauseCounter++;
        proofNodes.put(node.getName(), node);

        if (node.isGoodDefinitionOfBadLiteral()) {
            assert (!goodDefinitionsOfBadLiterals.contains(node));
            goodDefinitionsOfBadLiterals.add(node);
        }

    }

    /**
     * get the number of literal Conclusions in all VeriTProofNodes attached to
     * this VeritProof
     * 
     * @return the number of literal Conclusions in all VeriTProofNodes attached
     *         to this VeritProof
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
     * removes a proofSet in the VeritProof. It is detached from all its
     * children and from all its parents.
     * 
     * @param proofNode
     */
    @Deprecated
    public void removeProofSet(VeritProofNode proofNode) {
        if (proofNode.getParents() != null)
            for (VeritProofNode parent : proofNode.getParents())
                parent.removeSubProof(proofNode);
        if (proofNode.getSubProofs() != null)
            for (VeritProofNode subproof : proofNode.getSubProofs())
                subproof.removeParent(proofNode);

        if (proofNode.isGoodDefinitionOfBadLiteral()) {
            assert (goodDefinitionsOfBadLiterals.contains(proofNode));
            goodDefinitionsOfBadLiterals.remove(proofNode);
            assert (!goodDefinitionsOfBadLiterals.contains(proofNode));
        }
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
        // goodDefinitionsOfBadLiterals.remove(node);
        // Workaround because removal seems to be broken
        Set<VeritProofNode> tmp = new HashSet<VeritProofNode>();
        for (VeritProofNode otherNode : goodDefinitionsOfBadLiterals) {
            if (!otherNode.equals(node))
                tmp.add(otherNode);
        }
        goodDefinitionsOfBadLiterals.clear();
        goodDefinitionsOfBadLiterals.addAll(tmp);
        // End workaround
        assert (!goodDefinitionsOfBadLiterals.contains(node));

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
     * 
     * @return one good definition of a bad literal occurring in this proof, or
     *         <code>null</code> if no such node exists.
     */
    @SuppressWarnings("unused")
    private VeritProofNode getOneGoodDefinitionOfBadLiteral() {
        return goodDefinitionsOfBadLiterals.isEmpty() ? null
                : goodDefinitionsOfBadLiterals.iterator().next();
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

        for (VeritProofNode node : goodDefinitionsOfBadLiterals) {
            if (proofNodes.get(node.getName()) != node)
                return false;
        }

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

    // /**
    // *
    // * @return a node in this proof that proves <code>false</code>, or
    // * <code>null</code> if no such node exists
    // */
    // public VeritProofNode findNodeProvingFalse() {
    // WeakReference<VeritProofNode> reference = nodeCache.get(ImmutableSet
    // .create(new HashSet<Formula>()));
    // return reference == null ? null : reference.get();
    // }

    /**
     * Cleans the proof of bad literals and splits leafs into colorable parts.
     */
    public void cleanProof() {
        // assert (this.checkProof());
        // Util.printToSystemOutWithWallClockTimePrefix("Number of bad leafs to clean: "
        // + this.goodDefinitionsOfBadLiterals.size());
        // VeritProofNode currentLeaf = this.getOneGoodDefinitionOfBadLiteral();
        // while (currentLeaf != null) {
        // Util.printToSystemOutWithWallClockTimePrefix("  Cleaning leaf "
        // + currentLeaf.getName());
        // cleanProof(currentLeaf);
        // removeUnreachableNodes();
        // currentLeaf = this.getOneGoodDefinitionOfBadLiteral();
        // }
        // assert (this.hasNoBadLiterals());
        // assert (this.checkProof());

        Set<VeritProofNode> leafs = this.getLeafs();
        Util.printToSystemOutWithWallClockTimePrefix("Found " + leafs.size()
                + " leafs.");
        Set<VeritProofNode> leafsToClean = new HashSet<VeritProofNode>();

        for (VeritProofNode leaf : leafs) {
            Set<Integer> partitions = leaf.getPartitionsFromSymbols();
            partitions.remove(-1);
            if (partitions.size() > 1) {
                assert (leaf.isAxiom());
                leafsToClean.add(leaf);
            }
        }

        Util.printToSystemOutWithWallClockTimePrefix("  " + leafsToClean.size()
                + " need splitting.");
        int count = 0;
        for (VeritProofNode leafToClean : leafsToClean) {
            assert (CongruenceClosure.checkVeritProofNode(leafToClean));
            assert (Util.countPositiveLiterals(leafToClean
                    .getLiteralConclusions()) == 1);
            assert (Util.countPositiveLiterals(leafToClean
                    .getLiteralConclusions())
                    + Util.countNegativeLiterals(leafToClean
                            .getLiteralConclusions()) == leafToClean
                    .getLiteralConclusions().size());

            Formula positiveLiteral = Util.findPositiveLiteral(leafToClean
                    .getLiteralConclusions());
            assert (positiveLiteral != null);
            assert (positiveLiteral instanceof DomainEq || positiveLiteral instanceof UninterpretedPredicateInstance);

            VeritProofNode replacement = null;
            // if (leafToClean.getType().equals(VeriTToken.EQ_CONGRUENT)
            // || leafToClean.getType().equals(VeriTToken.EQ_TRANSITIVE)) {
            if (positiveLiteral instanceof DomainEq) {
                Util.printToSystemOutWithWallClockTimePrefix("    Splitting leaf "
                        + leafToClean.getName());
                TransitivityCongruenceChain chain = TransitivityCongruenceChain
                        .create(leafToClean);
                replacement = chain.toColorableProof();
                // } else if (leafToClean.getType().equals(
                // VeriTToken.EQ_CONGRUENT_PRED)) {
            } else if (positiveLiteral instanceof UninterpretedPredicateInstance) {
                Util.printToSystemOutWithWallClockTimePrefix("    Splitting (predicate) leaf "
                        + leafToClean.getName());
                replacement = leafToClean.splitPredicateLeaf();
            } else {
                Util.printToSystemOutWithWallClockTimePrefix("Unexpected implied literal:");
                System.out.println(positiveLiteral.toString());
                System.out.println("Containing leaf:");
                System.out.println(leafToClean.toString());
                assert (false);
            }
            assert (replacement != null);
            assert (leafToClean.getLiteralConclusions().containsAll(replacement
                    .getLiteralConclusions()));
            for (VeritProofNode parent : leafToClean.getParents())
                parent.makeStronger(leafToClean, replacement);
            Util.printToSystemOutWithWallClockTimePrefix("    Done " + ++count);
        }
        Util.printToSystemOutWithWallClockTimePrefix("  All done.");
        this.removeUnreachableNodes();
        assert (this.isColorable());
        assert (this.checkProof());
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
     * @return all leafs of this proof.
     */
    public Set<VeritProofNode> getLeafs() {
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
    @SuppressWarnings("unused")
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
                        this);
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
        resProof.tranformResProofs();

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
            List<Lit> resClause = new ArrayList<Lit>();
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
                    resProof.var_part.put(resLiteralID, partition < 0 ? 0
                            : partition);
                }
                resClause
                        .add(new Lit(resLiteralID, Util.getSignValue(literal)));
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
                resLeafNode = resProof.addLeaf(resClause, leafPartition);
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
     * Thus, using this number in the name of a new node guarantees that it is
     * unique.
     * 
     * @return the clause counter
     */
    public int getClauseCounter() {
        return clauseCounter;
    }

    /**
     * Returns the size of this proof. More precisely, returns the number of
     * nodes currently stored in the internal map <code>proofNodes</code>.
     * 
     * @return the number of nodes in this proof.
     */
    public int size() {
        return proofNodes.size();
    }

    /**
     * Returns a node name that does not yet exist in the proof. The name will
     * be of the form <code>prefix + number + suffix</code>, where number is
     * either the empty string or the smallest (positive) number such that the
     * name is fresh.
     * 
     * @param prefix
     * @param suffix
     * @return a node name that does not yet exist in the proof.
     */
    public String freshNodeName(String prefix, String suffix) {
        assert (prefix != null);
        assert (suffix != null);

        String name = prefix + suffix;
        if (!proofNodes.containsKey(name))
            return name;

        int number = 1;
        while (number > 0) {
            name = prefix + number + suffix;
            if (!proofNodes.containsKey(name))
                return name;
            number++;
        }
        // No fresh name found
        assert (false);
        return null;
    }

    // Methods for serialization/deserialization

    private void writeObject(java.io.ObjectOutputStream out) throws IOException {
        out.writeObject(proofNodes);
        out.writeObject(root);
        out.writeObject(goodDefinitionsOfBadLiterals);
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

            Field goodDefinitionsOfBadLiteralsField = VeritProof.class
                    .getDeclaredField("goodDefinitionsOfBadLiterals");
            goodDefinitionsOfBadLiteralsField.setAccessible(true);
            goodDefinitionsOfBadLiteralsField.set(this, in.readObject());
            goodDefinitionsOfBadLiteralsField.setAccessible(false);

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

}
