/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.util.ImmutableSet;
import at.iaik.suraq.util.Stack;
import at.iaik.suraq.util.Util;

/**
 * This Proof consists of several VeritProofNodes. You shall not try to modify
 * the parents/childs of these VeritProofNodes on your own. Use this class to
 * add/remove ProofNodes(=ProofSets)
 * 
 * @author chillebold
 * 
 */

public class VeritProof {

    /**
     * ProofSets = ProofNodes. The key is the name (e.g. ".c44")
     */
    protected final HashMap<String, VeritProofNode> proofSets = new HashMap<String, VeritProofNode>();

    /**
     * The root of the proof. Can only be set once.
     */
    protected VeritProofNode root = null;

    /**
     * A cache of nodes, indexed by their conclusions (represented as sets,
     * since order is immaterial).
     */
    private final WeakHashMap<ImmutableSet<Formula>, WeakReference<VeritProofNode>> nodeCache = new WeakHashMap<ImmutableSet<Formula>, WeakReference<VeritProofNode>>();

    /**
     * This stores all <em>leaf</em> nodes where several good literals define a
     * bad literal. E.g. a!=b v b!=c v a=c, for a=c being a bad literal and a=b,
     * b=c being good literals.
     */
    private final HashSet<VeritProofNode> goodDefinitionsOfBadLiterals = new HashSet<VeritProofNode>();

    /**
     * Generates and returns a new VeritProofNode. It is automatically attached
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
     * @return the newly created proof node
     */
    public VeritProofNode addProofSet(String name, Token type,
            List<Formula> conclusions, List<VeritProofNode> clauses,
            Integer iargs) {
        return addProofSet(name, type, conclusions, clauses, iargs, false);
    }

    /**
     * Returns a (new) <code>VeritProofNode</code>. It is automatically attached
     * to its clauses (as a Parent). Then the generated VeritProofNode is
     * returned. If <code>checkCache</code> is set to <code>true</code>, the
     * <code>nodeCache</code> is checked for a fitting node before a new one is
     * created.
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
     * @param checkCache
     *            check the cache for a fitting existing node, before creating a
     *            new one.
     * @return the requested proof node.
     */
    public VeritProofNode addProofSet(String name, Token type,
            List<Formula> conclusions, List<VeritProofNode> clauses,
            Integer iargs, boolean checkCache) {

        if (proofSets.keySet().contains(name))
            throw new RuntimeException("Name of proof node is not unique.");

        VeritProofNode node = null;
        if (checkCache) {
            WeakReference<VeritProofNode> reference = nodeCache
                    .get(ImmutableSet.create(conclusions));
            if (reference != null) {
                node = reference.get();
            }
        }
        if (node == null)
            node = new VeritProofNode(name, type, conclusions, clauses, iargs,
                    this);

        proofSets.put(name, node);
        nodeCache.put(ImmutableSet.create(conclusions),
                new WeakReference<VeritProofNode>(node));

        if (clauses != null) {
            for (VeritProofNode clause : clauses) {
                clause.addParent(node);
            }
        }

        if (node.isGoodDefinitionOfBadLiteral()) {
            assert (!goodDefinitionsOfBadLiterals.contains(node));
            goodDefinitionsOfBadLiterals.add(node);
        }

        return node;
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
        for (VeritProofNode proofSet : proofSets.values()) {
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
        proofSets.remove(proofNode.getName());
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
        proofSets.remove(node.getName());
        goodDefinitionsOfBadLiterals.remove(node);
        removeFromCache(node);
    }

    /**
     * Removes the given <code>node</code> from the <code>nodeCache</code> if it
     * is there.
     * 
     * @param node
     */
    private void removeFromCache(VeritProofNode node) {
        assert (node != null);
        if (!nodeCache.keySet().contains(node.getLiteralConclusionsAsSet()))
            return;
        VeritProofNode cacheEntry = nodeCache.get(
                node.getLiteralConclusionsAsSet()).get();
        if (cacheEntry == node) {
            nodeCache.remove(node.getLiteralConclusionsAsSet());
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
        return proofSets.get(name);
    }

    /**
     * Returns a non-Mutable HashSet of ProofSets
     * 
     * @return an immutable set of all nodes of this proof
     */
    public ImmutableSet<VeritProofNode> getProofNodes() {
        return ImmutableSet.create(proofSets.values());
    }

    /**
     * 
     * @return one good definition of a bad literal occurring in this proof, or
     *         <code>null</code> if no such node exists.
     */
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
    public boolean isClean() {
        for (VeritProofNode node : proofSets.values()) {
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
     * in the proofSets</li>
     * <li>The root is not <code>null</code>, and belongs to the proofSets</li>
     * <li>The root has no parents</li>
     * <li>All nodes, except the root, have at least one parent</li>
     * <li>For each node in the proofSets, there is a node with the same
     * conclusion in the nodeCache</li>
     * </ul>
     * Easy checks are performed first (early fail strategy).
     * 
     * @return <code>true</code> if this proof checks out correct.
     */
    public boolean checkProof() {
        if (root == null)
            return false;
        if (!root.getParents().isEmpty())
            return false;
        if (proofSets.get(root.getName()) != root)
            return false;

        for (VeritProofNode node : proofSets.values()) {
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

            if (nodeCache.get(node.getLiteralConclusionsAsSet()) == null)
                return false;
            else if (nodeCache.get(node.getLiteralConclusionsAsSet()).get() == null)
                return false;

            if (!node.checkProofNode())
                return false;
        }

        for (VeritProofNode node : goodDefinitionsOfBadLiterals) {
            if (proofSets.get(node.getName()) != node)
                return false;
        }

        for (WeakReference<VeritProofNode> reference : nodeCache.values()) {
            if (reference.get() != null) {
                if (proofSets.get(reference.get().getName()) != reference.get())
                    return false;
            }
        }

        // All checks passed
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
     * Sets the root of this proof, unless it is already set.
     * 
     * @param root
     *            the root to set. Must be a node of this proof and may not have
     *            parents.
     * @return <code>true</code> if the given root was set, <code>false</code>
     *         if a root was already set earlier, or the given root does not
     *         belong to this proof, or has parents, and thus no change was
     *         done.
     */
    public boolean setRoot(VeritProofNode root) {
        if (this.root == null) {
            if (!proofSets.values().contains(root))
                return false;
            if (!root.getParents().isEmpty())
                return false;
            if (root.getProof() != this)
                return false;
            this.root = root;
            return true;
        }
        return false;
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
                proofSets.values());
        unreachableNodes.removeAll(reachableNodes);

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
            for (VeritProofNode child : unreachableNode.getSubProofs()) {
                child.removeParent(unreachableNode);
                assert (!child.getParents().isEmpty() || unreachableNodes
                        .contains(child));
            }
            // removing the node
            assert (proofSets.get(unreachableNode.getName()) == unreachableNode);
            proofSets.remove(unreachableNode.getName());
            goodDefinitionsOfBadLiterals.remove(unreachableNode);
            removeFromCache(unreachableNode);
        }
        // Done. Just some final assertions.
        assert (proofSets.size() == reachableNodes.size());
        assert (proofSets.values().equals(reachableNodes));
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
     * 
     * @return a node in this proof that proves <code>false</code>, or
     *         <code>null</code> if no such node exists
     */
    public VeritProofNode findNodeProvingFalse() {
        WeakReference<VeritProofNode> reference = nodeCache.get(ImmutableSet
                .create(new HashSet<Formula>()));
        return reference == null ? null : reference.get();
    }

    /**
     * Cleans the proof of bad literals
     */
    public void cleanProof() {
        VeritProofNode currentLeaf = this.getOneGoodDefinitionOfBadLiteral();
        while (currentLeaf != null) {
            cleanProof(currentLeaf);
            assert (!this.proofSets.values().contains(currentLeaf));
            assert (!this.goodDefinitionsOfBadLiterals.contains(currentLeaf));
            currentLeaf = this.getOneGoodDefinitionOfBadLiteral();
        }
        assert (this.isClean());
        assert (this.checkProof());
    }

    /**
     * Rewrites the proof to get rid of the given bad literal definition.
     * 
     * @param currentLeaf
     *            a good definition of a bad literal
     */
    private void cleanProof(VeritProofNode currentLeaf) {
        assert (currentLeaf.isLeaf());
        assert (currentLeaf.isGoodDefinitionOfBadLiteral());

        Formula badLiteral = currentLeaf.getDefinedBadLiteral();
        assert (badLiteral != null);
        Formula inverseBadLiteral = Util.invertLiteral(badLiteral);
        List<Formula> definingLiterals = currentLeaf.getDefiningGoodLiterals();
        assert (definingLiterals != null);

        Map<Formula, VeritProofNode> resolvedDefiningLiterals = new HashMap<Formula, VeritProofNode>();

        // Search for resolution of bad literal
        VeritProofNode currentNode = currentLeaf;
        while (!currentNode.resolvesOn(badLiteral)) {
            assert (!currentNode.getParents().isEmpty());

            Formula resolvingLiteral = currentNode.findResolvingLiteral();
            Formula definingLiteral = null;
            if (definingLiterals.contains(resolvingLiteral))
                definingLiteral = resolvingLiteral;
            if (definingLiterals.contains(Util.invertLiteral(resolvingLiteral)))
                definingLiteral = Util.invertLiteral(resolvingLiteral);
            if (definingLiteral != null) {
                // Record which definition literals are resolved along the path
                if (currentNode.resolvesOn(definingLiteral))
                    resolvedDefiningLiterals
                            .put(definingLiteral,
                                    currentNode
                                            .getChildWithLiteralInOppositePolarity(definingLiteral));
            }
            currentNode = currentNode.getParents().get(0);
        }

        // Go back up the other way, record the path
        Stack<VeritProofNode> path = new Stack<VeritProofNode>();
        while (!currentNode.getSubProofs().isEmpty()) {
            for (VeritProofNode currentChild : currentNode.getSubProofs()) {
                if (currentChild.getLiteralConclusionsAsSet().contains(
                        inverseBadLiteral)) {
                    currentNode = currentChild;
                    path.push(currentNode);
                    break;
                }
            }
        }
        assert (currentNode.getSubProofs().isEmpty());

        // Replace nodes on the path
        currentNode = path.pop();
        while (!path.isEmpty()) {
            VeritProofNode nextNode = path.pop();

            List<Formula> newConclusion = new ArrayList<Formula>();
            for (Formula literal : currentNode.getLiteralConclusions()) {
                if (literal.equals(inverseBadLiteral))
                    newConclusion.addAll(definingLiterals);
                else
                    newConclusion.add(literal);
            }

            // TODO

            currentNode = nextNode;
        }

    }
}
