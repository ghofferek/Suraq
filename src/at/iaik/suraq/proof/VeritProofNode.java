/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.util.ImmutableArrayList;
import at.iaik.suraq.util.ImmutableSet;
import at.iaik.suraq.util.Util;

/**
 * VeritProofSet is a single set-line in the proof. You shall not use this class
 * to create or modify the proof. Use VeritProof instead. To prevent you from
 * using certain functions, they are marked as deprecated.
 * 
 * @author chillebold
 * 
 */
public class VeritProofNode {
    /**
     * The name of the VeritProofNode. E.g. ".c11"
     */
    private final String name;

    /**
     * The type of the VeritProofNode. It should be one of the Types defined in
     * VeriTToken. E.g. VeriTToken.EQ_TRANSITIVE
     */
    private final Token type;

    /**
     * A list of literalConclusions (Formulas). The contents of this list should
     * not be changed!
     */
    private final List<Formula> literalConclusions;

    /**
     * iargs (Integer)
     */
    private final Integer iargs;

    /**
     * A list of SubProofs/Conclusions
     */
    private final List<VeritProofNode> subProofs;

    /**
     * A list of Parents
     */
    private final List<VeritProofNode> parents;

    /**
     * Do not call this constructor by yourself. Use VeritProof to create this
     * class.
     * 
     * @param name
     * @param type
     * @param conclusions
     * @param clauses
     * @param iargs
     */
    @Deprecated
    protected VeritProofNode(String name, Token type,
            List<Formula> conclusions, List<VeritProofNode> clauses,
            Integer iargs) {
        this.name = name;
        this.type = type;
        this.literalConclusions = conclusions == null ? null
                : new ArrayList<Formula>(conclusions);
        this.subProofs = clauses == null ? null
                : new ArrayList<VeritProofNode>(clauses);
        this.parents = new ArrayList<VeritProofNode>();
        this.iargs = iargs;
    }

    public String getName() {
        return name;
    }

    public Token getType() {
        return type;
    }

    /**
     * This method returns the inner conclusions-List. If you modify elements in
     * this list or the list itself, also this object changes! Notice the method
     * getConclusionCopy()
     * 
     * @return
     */
    @Deprecated
    public List<Formula> getLiteralConclusions() {
        return literalConclusions;
    }

    /**
     * This method returns a copy of the inner conclusions-List.
     * 
     * @return a copied ArrayList of the conclusions
     */
    public List<Formula> getLiteralConclusionsCopy() {
        return new ArrayList<Formula>(literalConclusions);
    }

    /**
     * This method returns an OR-Formula of the literal conclusions
     * 
     * @return a copied ArrayList of the conclusions
     */
    public OrFormula getConclusions() {
        return OrFormula.generate(literalConclusions);
    }

    /**
     * returns an immutable copy of clauses. You cannot modify the list
     * direclty. Use the VeritProof-Class instead!
     * 
     * @return
     */
    public ImmutableArrayList<VeritProofNode> getSubProofs() {
        if (subProofs == null)
            return null;
        return new ImmutableArrayList<VeritProofNode>(subProofs);
    }

    public Integer getIargs() {
        return iargs;
    }

    /**
     * returns an immutable copy of parents. You cannot modify the list
     * directly. Use the VeritProof-Class instead!
     * 
     * @return
     */
    public ImmutableArrayList<VeritProofNode> getParents() {
        if (parents == null)
            return null;
        return new ImmutableArrayList<VeritProofNode>(parents);
    }

    @Deprecated
    protected void addParent(VeritProofNode parent) {
        parents.add(parent);
    }

    @Deprecated
    protected boolean removeParent(VeritProofNode parent) {
        return parents.remove(parent);
    }

    @Deprecated
    protected void addSubProof(VeritProofNode subProof) {
        subProofs.add(subProof);
    }

    @Deprecated
    protected boolean removeSubProof(VeritProofNode subProof) {
        return subProofs.remove(subProof);
    }

    @Override
    public String toString() {
        String str = "(set " + name + " (" + type;
        if (subProofs != null) {
            str += " :clauses (";
            for (VeritProofNode clause : subProofs)
                str += clause.getName() + " ";
            str += ")";
        }
        if (iargs != null) {
            str += " :iargs (" + iargs + ")";
        }
        if (literalConclusions != null) {
            str += " :conclusions (";
            for (Formula conclusion : literalConclusions)
                str += " " + conclusion.toString();
            str += ")";
        }
        str += "))";
        return str;
    }

    /**
     * Checks if the current proof node's conclusion is correctly derived from
     * all its sub-proofs.
     * 
     * @return <code>true</code> if this node is a valid deduction,
     *         <code>false</code> otherwise.
     */
    public boolean checkProofNode() {
        // TODO
        assert (false);
        return false;
    }

    /**
     * 
     * @return <code>true</code>, if the conclusion of this node contains a bad
     *         literal.
     */
    public boolean containsBadLiteral() {
        for (Formula literal : literalConclusions) {
            if (Util.isBadLiteral(literal))
                return true;
        }
        return false;
    }

    /**
     * Checks if the conclusion of this node is an axiom that introduces a new
     * bad literal based solely on good literals.
     * 
     * @return <code>true</code> if this node is a leaf with a conclusion that
     *         has one positive bad literal and only negative good literals.
     */
    public boolean isGoodDefinitionOfBadLiteral() {
        if (subProofs.size() > 0)
            return false; // Not a leaf

        if (literalConclusions.size() < 2)
            return false; // Not a definition if there is just one literal

        for (Formula literal : literalConclusions) {
            if (Util.isNegativeLiteral(literal)) {
                if (Util.isBadLiteral(literal))
                    return false; // bad literal should occur positive
            } else if (Util.isLiteral(literal)) {
                if (!Util.isBadLiteral(literal))
                    return false; // positive literal should be bad
            } else {
                // This means we have something that is not a literal.
                // That should not happen.
                assert (false);
            }
        }
        return true;
    }

    /**
     * @return <code>true</code> if this is a leaf.
     */
    public boolean isLeaf() {
        return subProofs.size() == 0;
    }

    /**
     * 
     * @return the defined bad literal, or <code>null</code> if this node does
     *         not define a bad literal by good ones.
     */
    public Formula getDefinedBadLiteral() {
        if (!isGoodDefinitionOfBadLiteral())
            return null;
        for (Formula literal : literalConclusions) {
            assert (Util.isLiteral(literal));
            if (Util.isBadLiteral(literal))
                return literal;
        }
        assert (false);
        return null;
    }

    /**
     * 
     * @return the set of good literals defining a bad one, or <code>null</code>
     *         if this node is not a good definition of a bad literal
     */
    public ImmutableSet<Formula> getDefiningGoodLiteral() {
        if (!isGoodDefinitionOfBadLiteral())
            return null;
        HashSet<Formula> tmp = new HashSet<Formula>();
        for (Formula literal : literalConclusions) {
            assert (Util.isLiteral(literal));
            if (!Util.isBadLiteral(literal))
                tmp.add(literal);
        }
        assert (!tmp.isEmpty());
        return ImmutableSet.create(tmp);
    }

}
