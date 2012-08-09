package at.iaik.suraq.proof;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.util.ImmutableArrayList;

/**
 * VeritProofSet is a single set-line in the proof. You shall not use this class
 * to create or modify the proof. Use VeritProof instead. To prevent you from
 * using certain functions, they are marked as deprecated.
 * 
 * @author chillebold
 * 
 */
public class VeritProofNode {
    private final String name;
    private final Token type;
    private final List<Formula> literalConclusions;
    private final Integer iargs;
    private final List<VeritProofNode> subProofs;
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
        if(subProofs == null)
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
        if(parents == null)
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

}
