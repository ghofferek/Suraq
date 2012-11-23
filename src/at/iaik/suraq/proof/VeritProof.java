/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.util.ImmutableHashSet;

/**
 * This Proof consists of several VeritProofNodes. You shall not try to modify
 * the parents/childs of these VeritProofNodes on your own. Use this class to
 * add/remove ProofNodes(=ProofSets)
 * 
 * @author chillebold
 * 
 */
@SuppressWarnings("deprecation")
public class VeritProof {

    /**
     * ProofSets = ProofNodes. The key is the name (e.g. ".c44")
     */
    protected final HashMap<String, VeritProofNode> proofSets = new HashMap<String, VeritProofNode>();

    /**
     * This stores all <em>leaf</em> nodes where several good literals define a
     * bad literal. E.g. a!=b v b!=c v a=c, for a=c being a bad literal and a=b,
     * b=c being good literals.
     */
    private final HashSet<VeritProofNode> leafsDefiningBadLiteralViaGoodLiterals = new HashSet<VeritProofNode>();

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
     * @return
     */
    public VeritProofNode addProofSet(String name, Token type,
            List<Formula> conclusions, List<VeritProofNode> clauses,
            Integer iargs) {
        VeritProofNode tmp = new VeritProofNode(name, type, conclusions,
                clauses, iargs);

        proofSets.put(name, tmp);

        if (clauses != null) {
            for (VeritProofNode clause : clauses) {
                clause.addParent(tmp);
            }
        }

        // TODO check for leaf defining bad literal; if so, add to corresponding
        // set

        return tmp;
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
    public void removeProofSet(VeritProofNode proofNode) {
        if (proofNode.getParents() != null)
            for (VeritProofNode parent : proofNode.getParents())
                parent.removeSubProof(proofNode);
        if (proofNode.getSubProofs() != null)
            for (VeritProofNode subproof : proofNode.getSubProofs())
                subproof.removeParent(proofNode);

        // TODO check for leaf defining bad literal; if so, remove from
        // corresponding set
        proofSets.remove(proofNode.getName());
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
     * returns all VeritProofNodes in a Collection.
     * 
     * @return
     */
    public Collection<VeritProofNode> getProofNodes() {
        return proofSets.values();
    }

    /**
     * Returns a non-Mutable HashSet of ProofSets
     * 
     * @return
     */
    public ImmutableHashSet<VeritProofNode> getProofIterator() {
        return new ImmutableHashSet<VeritProofNode>(proofSets.values());
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
        for (VeritProofNode proof : getProofIterator())
            str = str.append(proof.toString() + "\n");
        return str.toString();
    }

}
