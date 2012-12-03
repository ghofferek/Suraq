/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
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
    private final ImmutableArrayList<Formula> literalConclusions;

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
     * The proof this node belongs to.
     */
    private final VeritProof proof;

    /**
     * Do not call this constructor by yourself. Use VeritProof to create this
     * class.
     * 
     * @param name
     * @param type
     * @param conclusions
     * @param clauses
     * @param iargs
     * @param proof
     */
    protected VeritProofNode(String name, Token type,
            List<Formula> conclusions, List<VeritProofNode> clauses,
            Integer iargs, VeritProof proof) {
        this.name = name;
        this.type = type;
        this.literalConclusions = conclusions == null ? new ImmutableArrayList<Formula>()
                : new ImmutableArrayList<Formula>(conclusions);
        this.subProofs = clauses == null ? new ArrayList<VeritProofNode>()
                : new ArrayList<VeritProofNode>(clauses);
        this.parents = new ArrayList<VeritProofNode>();
        this.iargs = iargs;
        this.proof = proof;
    }

    public String getName() {
        return name;
    }

    public Token getType() {
        return type;
    }

    /**
     * This method returns the inner conclusions-List.
     * 
     * @return the list of literals in the conclusions.
     */

    public ImmutableArrayList<Formula> getLiteralConclusions() {
        return literalConclusions;
    }

    /**
     * This method returns the inner conclusions-List as a set.
     * 
     * @return the list of literals in the conclusions in set representation.
     */

    public ImmutableSet<Formula> getLiteralConclusionsAsSet() {
        return ImmutableSet.create(literalConclusions);
    }

    /**
     * This method returns an OR-Formula of the literal conclusions
     * 
     * @return a copied ArrayList of the conclusions
     */
    public OrFormula getConclusionsAsOrFormula() {
        return OrFormula.generate(literalConclusions);
    }

    /**
     * returns an immutable copy of clauses. You cannot modify the list
     * directly. Use the VeritProof-Class instead!
     * 
     * @return an immutable copy of the subproofs, or <code>null</code> if this
     *         is a leaf.
     */
    public ImmutableArrayList<VeritProofNode> getSubProofs() {
        if (subProofs == null)
            return null;
        return new ImmutableArrayList<VeritProofNode>(subProofs);
    }

    /**
     * 
     * @return the <code>iargs</code> property, or <code>null</code> if not
     *         present.
     */
    public Integer getIargs() {
        return iargs;
    }

    /**
     * returns an immutable copy of parents. You cannot modify the list
     * directly. Use the VeritProof-Class instead!
     * 
     * @return an immutable copy of parents. Will be empty if this is a/the root
     *         node.
     */
    public ImmutableArrayList<VeritProofNode> getParents() {
        assert (parents != null);
        return new ImmutableArrayList<VeritProofNode>(parents);
    }

    /**
     * Adds a node to the list of parents of <code>this</code> node.
     * <code>this</code> node has to be in the <code>subProofs</code> of the
     * given <code>parent</code>.
     * 
     * @param parent
     *            a parent of this node
     */
    protected void addParent(VeritProofNode parent) {
        assert (parent.subProofs.contains(this));
        parents.add(parent);
    }

    /**
     * Removes the given <code>parent</code> from the list of parents.
     * <code>this</code> node may not show up in the <code>subProofs</code> of
     * the <code>parent</code>. If the given <code>parent</code> is not present
     * in the current list of parents, nothing happens.
     * 
     * @param parent
     *            the parent to remove
     */
    protected void removeParent(VeritProofNode parent) {
        if (parents.contains(parent)) {
            assert (!parent.subProofs.contains(this));
            parents.remove(parent);
            if (parents.isEmpty())
                this.kill();
        }

    }

    /**
     * Clears the subproofs, removes <code>this</code> from the parents of all
     * subproofs, and removes this dangling node from its proof. <strong>Only
     * call on nodes without parents!</strong>
     */
    private void kill() {
        assert (parents.isEmpty());
        this.proof.removeDanglingProofNode(this);
        List<VeritProofNode> tmpSubProofs = new ArrayList<VeritProofNode>(
                subProofs);
        subProofs.clear();
        for (VeritProofNode subProof : tmpSubProofs) {
            subProof.removeParent(this);
        }
    }

    @Deprecated
    protected void addSubProof(VeritProofNode subProof) {
        subProofs.add(subProof);
        assert (this.checkProofNode());
    }

    @Deprecated
    protected void removeSubProof(VeritProofNode subProof) {
        subProofs.remove(subProof);
        assert (this.checkProofNode());
    }

    /**
     * Replaces <code>oldSubProof</code> with <code>newSubProof</code> in the
     * subproofs of <code>this</code>. The conclusion of
     * <code>oldSubProof</code> and <code>newSubProof</code> have to be the
     * same. None of the parameters may be <code>null</code>.
     * 
     * @param oldSubProof
     *            the subproof to remove
     * @param newSubProof
     *            the subproof to put it instead
     */
    protected boolean updateProofNode(VeritProofNode oldSubProof,
            VeritProofNode newSubProof) {
        assert (oldSubProof != null);
        assert (newSubProof != null);
        assert (oldSubProof.getParents().contains(this));

        if (!((this.subProofs.contains(oldSubProof)) && (oldSubProof
                .getLiteralConclusionsAsSet().equals(newSubProof
                .getLiteralConclusionsAsSet())))) {
            return false;
        }

        subProofs.set(subProofs.indexOf(oldSubProof), newSubProof);

        assert (checkProofNode());

        oldSubProof.removeParent(this);
        newSubProof.addParent(this);
        return true;
    }

    /**
     * Updates the subproofs of <code>this</code> node to the given ones. The
     * node is checked after replacement. If the check fails, changes are
     * reverted and <code>false</code> is returned. Parent relations are also
     * updated accordingly, if update is successful.
     * 
     * @param newSubProofs
     *            the new subproofs to set.
     * @return <code>true</code> if replacement was successful and actually
     *         done; <code>false</code> if replacement failed and changes have
     *         been reverted.
     */
    protected boolean updateProofNode(List<VeritProofNode> newSubProofs) {
        List<VeritProofNode> tmpSubProofs = new ArrayList<VeritProofNode>(
                subProofs);
        subProofs.clear();
        subProofs.addAll(newSubProofs);
        if (!checkProofNode()) {
            subProofs.clear();
            subProofs.addAll(tmpSubProofs);
            return false;
        }

        for (VeritProofNode oldSubProof : tmpSubProofs)
            oldSubProof.removeParent(this);

        for (VeritProofNode newSubProof : subProofs)
            newSubProof.addParent(this);
        return true;
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

        // General pre-tests

        for (Formula literal : literalConclusions) {
            if (!Util.isLiteral(literal))
                return false;
        }

        // Type specific tests

        if (this.type.equals(VeriTToken.INPUT)) {
            if (subProofs.size() != 0)
                return false;
            return true;
        }

        if (this.type.equals(VeriTToken.AND)) {
            // This type should not occur
            assert (false);
            return false;
        }

        if (this.type.equals(VeriTToken.OR)) {
            // This type should not occur
            assert (false);
            return false;
        }

        if (this.type.equals(VeriTToken.EQ_REFLEXIVE)) {
            if (subProofs.size() != 0)
                return false;
            if (literalConclusions.size() != 1)
                return false;
            assert (literalConclusions.size() == 1);
            Formula literal = literalConclusions.get(0);
            return Util.isReflexivity(literal);
        }

        if (this.type.equals(VeriTToken.EQ_CONGRUENT)) {
            return checkCongruence();
        }

        if (this.type.equals(VeriTToken.EQ_CONGRUENT_PRED)) {
            return checkCongruence();
        }

        if (this.type.equals(VeriTToken.EQ_TRANSITIVE)) {
            return checkTransitive();
        }

        if (this.type.equals(VeriTToken.RESOLUTION)) {
            return checkResolution();
        }

        // unknown node type
        assert (false);
        return false;
    }

    /**
     * Call only on nodes with type <code>RESOLUTION</code>.
     * 
     * @return <code>true</code> iff this is a valid resolution step
     */
    private boolean checkResolution() {

        assert (this.type.equals(VeriTToken.RESOLUTION));

        // Taking the assumption that only resolution with two children occurs.

        if (subProofs.size() != 2)
            return false;

        boolean resolvingLiteralFound = false;
        for (Formula literal : subProofs.get(0).literalConclusions) {
            if (!literalConclusions.contains(literal)) {
                if (resolvingLiteralFound)
                    return false;
                Formula invertedLiteral = Util.invertLiteral(literal);
                if (!subProofs.get(1).literalConclusions
                        .contains(invertedLiteral))
                    return false;
                else
                    resolvingLiteralFound = true;
            }
        }
        resolvingLiteralFound = false;
        for (Formula literal : subProofs.get(1).literalConclusions) {
            if (!literalConclusions.contains(literal)) {
                if (resolvingLiteralFound)
                    return false;
                Formula invertedLiteral = Util.invertLiteral(literal);
                if (!subProofs.get(0).literalConclusions
                        .contains(invertedLiteral))
                    return false;
                else
                    resolvingLiteralFound = true;
            }
        }
        for (Formula literal : literalConclusions) {
            if (!subProofs.get(0).literalConclusions.contains(literal)
                    && !subProofs.get(1).literalConclusions.contains(literal))
                return false;
        }
        return true;
    }

    /**
     * Call only on nodes with type <code>EQ_TRANSITIVE</code>.
     * 
     * @return <code>true</code> iff this is a valid transitivity axiom
     *         instantiation.
     */
    private boolean checkTransitive() {
        assert (this.type.equals(VeriTToken.EQ_TRANSITIVE));
        if (literalConclusions.size() < 3)
            return false;
        if (subProofs.size() != 0)
            return false;

        // Taking the assumption that the implied literal is the last one
        Formula impliedLiteral = literalConclusions.get(literalConclusions
                .size() - 1);
        if (Util.isNegativeLiteral(impliedLiteral))
            return false;
        if (!(impliedLiteral instanceof EqualityFormula))
            return false;
        if (!((EqualityFormula) impliedLiteral).isEqual())
            return false;
        Term[] terms = (Term[]) ((EqualityFormula) impliedLiteral).getTerms()
                .toArray();
        if (terms.length != 2)
            return false;

        for (Formula literal : literalConclusions.subList(0,
                literalConclusions.size() - 2)) {
            if (!Util.isLiteral(literal))
                return false;
            if (Util.isNegativeLiteral(literal))
                return false;
            if (!(literal instanceof EqualityFormula))
                return false;
            if (!((EqualityFormula) literal).isEqual())
                return false;
            if (((EqualityFormula) literal).getTerms().size() != 2)
                return false;
        }

        // Taking the assumption that the literals already form
        // a nice transitivity chain
        if (!((EqualityFormula) literalConclusions.get(0)).getTerms().get(1)
                .equals(terms[0]))
            return false;

        Term currentLink = ((EqualityFormula) literalConclusions.get(0))
                .getTerms().get(1);
        for (int count = 1; count < literalConclusions.size() - 1; count++) {
            if (!currentLink.equals(((EqualityFormula) literalConclusions
                    .get(count)).getTerms().get(0)))
                return false;
            currentLink = ((EqualityFormula) literalConclusions.get(count))
                    .getTerms().get(1);
        }
        if (!currentLink.equals(terms[1]))
            return false;

        return true;
    }

    /**
     * Call only on nodes with type <code>EQ_CONGRUENT</code> or
     * <code>EQ_CONGRUENT_PRED</code>.
     * 
     * @return <code>true</code>, iff this is a valid congruence axiom
     *         instantiation.
     */
    private boolean checkCongruence() {
        assert (this.type.equals(VeriTToken.EQ_CONGRUENT) || this.type
                .equals(VeriTToken.EQ_CONGRUENT_PRED));

        if (literalConclusions.size() < 2)
            return false;
        if (subProofs.size() != 0)
            return false;

        // Taking the assumption that the "implied literal" is the last one.
        Formula impliedLiteral = literalConclusions.get(literalConclusions
                .size() - 1);
        if (Util.isNegativeLiteral(impliedLiteral))
            return false;

        if (!(impliedLiteral instanceof EqualityFormula))
            return false;

        if (!((EqualityFormula) impliedLiteral).isEqual())
            return false;

        Term[] terms = (Term[]) ((EqualityFormula) impliedLiteral).getTerms()
                .toArray();

        if (terms.length != 2)
            return false;

        List<DomainTerm> terms1 = null;
        List<DomainTerm> terms2 = null;

        if (terms[0] instanceof UninterpretedFunctionInstance) {
            if (!(terms[1] instanceof UninterpretedFunctionInstance))
                return false;
            terms1 = ((UninterpretedFunctionInstance) terms[0]).getParameters();
            terms2 = ((UninterpretedFunctionInstance) terms[1]).getParameters();
            assert (terms1 != null);
            assert (terms2 != null);
            if (terms1.size() != terms2.size())
                return false;
            if (!((UninterpretedFunctionInstance) terms[0]).getFunction()
                    .equals(((UninterpretedFunctionInstance) terms[1])
                            .getFunction()))
                return false;
        }
        if (terms[0] instanceof UninterpretedPredicateInstance) {
            if (!(terms[1] instanceof UninterpretedPredicateInstance))
                return false;
            terms1 = ((UninterpretedPredicateInstance) terms[0])
                    .getParameters();
            terms2 = ((UninterpretedPredicateInstance) terms[1])
                    .getParameters();
            assert (terms1 != null);
            assert (terms2 != null);
            if (terms1.size() != terms2.size())
                return false;
            if (!((UninterpretedPredicateInstance) terms[0]).getFunction()
                    .equals(((UninterpretedPredicateInstance) terms[1])
                            .getFunction()))
                return false;
        }

        assert (terms1 != null);
        assert (terms2 != null);
        assert (terms1.size() == terms2.size());

        if (terms1.size() != literalConclusions.size() - 1)
            return false;

        // Taking the assumption that equalities in the axiom instantiation
        // occur in the same order as they occur as parameters to the
        // uninterpreted function
        for (int count = 0; count < terms1.size(); count++) {
            Formula literal = literalConclusions.get(count);
            if (!Util.isLiteral(literal))
                return false;
            if (!Util.isNegativeLiteral(literal))
                return false;
            assert (Util.makeLiteralPositive(literal) instanceof EqualityFormula);
            EqualityFormula eqLiteral = (EqualityFormula) Util
                    .makeLiteralPositive(literal);
            if (!eqLiteral.isEqual())
                return false;
            Term[] literalTerms = (Term[]) eqLiteral.getTerms().toArray();
            if (literalTerms.length != 2)
                return false;

            // Taking the assumption that the first term of the equality
            // corresponds
            // to a parameter on the first term of the impliedLiteral
            if (!terms1.get(count).equals(literalTerms[0]))
                return false;
            if (!terms2.get(count).equals(literalTerms[1]))
                return false;
        }
        return true;
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
        assert (subProofs != null);
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
