/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.lang.ref.WeakReference;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.WeakHashMap;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.util.ImmutableSet;
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
     * @return an immutable copy of the set of all nodes where a bad literal is
     *         defined in terms of good ones.
     */
    public ImmutableSet<VeritProofNode> getGoodDefinitionsOfBadLiterals() {
        return ImmutableSet.create(goodDefinitionsOfBadLiterals);
    }

    /**
     * 
     * @return one good definition of a bad literal occurring in this proof, or
     *         <code>null</code> if no such node exists.
     */
    public VeritProofNode getOneGoodDefinitionOfBadLiteral() {
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
     * @return <code>true</code> if all nodes in this proof are correct
     *         deductions.
     */
    public boolean checkProof() {
        for (VeritProofNode node : proofSets.values()) {
            if (!node.checkProofNode())
                return false;
        }
        return true;
    }

}
