/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;

import at.iaik.suraq.exceptions.IncomparableTermsException;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.util.CongruenceClosure;
import at.iaik.suraq.util.ImmutableArrayList;
import at.iaik.suraq.util.ImmutableSet;
import at.iaik.suraq.util.Util;
import at.iaik.suraq.util.graph.Graph;

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
    private final Set<VeritProofNode> parents;

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

        assert (name != null);
        this.name = name;
        this.type = type;

        List<Formula> reducedConclusions = new ArrayList<Formula>();
        for (Formula literal : conclusions) {
            if (!reducedConclusions.contains(literal))
                reducedConclusions.add(literal);
        }
        assert ((new HashSet<Formula>(reducedConclusions)).size() == reducedConclusions
                .size());

        List<VeritProofNode> tmpSubProofs = new ArrayList<VeritProofNode>();
        ArrayList<Formula> tmpLiteralConclusions = new ArrayList<Formula>();

        if (this.type.equals(VeriTToken.RESOLUTION) && clauses.size() > 2) {
            List<VeritProofNode> remainingClauses = new ArrayList<VeritProofNode>(
                    clauses);
            assert (!remainingClauses.isEmpty());
            tmpSubProofs.add(remainingClauses.remove(0));

            int count = 0;
            while (true) {
                count++;
                assert (!remainingClauses.isEmpty());
                assert (tmpSubProofs.size() == 1);
                assert (tmpLiteralConclusions.isEmpty());

                Formula literal = null;

                // Try using the "next" remaining clause
                literal = findResolvingLiteral(tmpSubProofs.get(0)
                        .getLiteralConclusions(), remainingClauses.get(0)
                        .getLiteralConclusions());
                if (literal != null) {
                    tmpSubProofs.add(remainingClauses.remove(0));
                } else { // Pick an arbitrary clause for resolution
                    literal = pickAndUseFittingClause(remainingClauses,
                            tmpSubProofs, reducedConclusions);
                }
                assert (tmpSubProofs.size() == 2);
                assert (literal != null);

                assert (tmpLiteralConclusions.isEmpty());
                for (Formula currentLiteral : tmpSubProofs.get(0)
                        .getLiteralConclusions()) {
                    if (!tmpLiteralConclusions.contains(currentLiteral))
                        tmpLiteralConclusions.add(currentLiteral);
                }
                for (Formula currentLiteral : tmpSubProofs.get(1)
                        .getLiteralConclusions()) {
                    if (!tmpLiteralConclusions.contains(currentLiteral))
                        tmpLiteralConclusions.add(currentLiteral);
                }
                tmpLiteralConclusions.remove(literal);
                tmpLiteralConclusions.remove(Util.invertLiteral(literal));

                if ((new HashSet<Formula>(tmpLiteralConclusions))
                        .equals(new HashSet<Formula>(reducedConclusions)))
                    break;

                VeritProofNode intermediateNode = null;

                // cache lookup
                if (proof != null) {
                    Matcher matcher = Util.digitsPattern.matcher(name);
                    String number = null;
                    if (matcher.find())
                        number = matcher.group(1);
                    else
                        assert (false);
                    intermediateNode = proof.cacheLookup(tmpLiteralConclusions,
                            number);
                }
                if (intermediateNode == null) {
                    intermediateNode = new VeritProofNode(name + "_i" + count,
                            VeriTToken.RESOLUTION, tmpLiteralConclusions,
                            tmpSubProofs, null, proof);
                }
                assert (intermediateNode != null);
                tmpSubProofs.clear();
                tmpSubProofs.add(intermediateNode);
                tmpLiteralConclusions.clear();
            }
            assert (remainingClauses.isEmpty());

        } else {
            tmpLiteralConclusions = reducedConclusions == null ? new ArrayList<Formula>()
                    : new ArrayList<Formula>(reducedConclusions);
            tmpSubProofs = clauses == null ? new ArrayList<VeritProofNode>()
                    : new ArrayList<VeritProofNode>(clauses);
        }

        assert (tmpLiteralConclusions != null);
        assert (tmpSubProofs != null);
        assert (tmpSubProofs.size() == 2 || !type.equals(VeriTToken.RESOLUTION));
        assert ((new HashSet<Formula>(tmpLiteralConclusions))
                .equals(new HashSet<Formula>(reducedConclusions)));
        this.subProofs = tmpSubProofs;
        this.literalConclusions = new ImmutableArrayList<Formula>(
                tmpLiteralConclusions);

        for (VeritProofNode child : this.subProofs)
            child.addParent(this);
        this.parents = new HashSet<VeritProofNode>();
        this.iargs = iargs == null ? null : new Integer(iargs);
        this.proof = proof;

        assert (this.checkProofNode());
        assert (proof != null);
        proof.addProofNode(this);
    }

    /**
     * Returns the literal that resolved the two given clauses, as it occurs in
     * <code>clause1</code>. A sanity check (that no other literals would be
     * resolving literals is <em>not</em> done.
     * 
     * @param clause1
     * @param clause2
     * @return the resolving literal (as it occurs in <code>clause1</code>
     *         polarity), or <code>null</code> if none exists
     */
    private Formula findResolvingLiteral(List<Formula> clause1,
            List<Formula> clause2) {
        for (Formula literal : clause1) {
            assert (Util.isLiteral(literal));
            Formula invertedLiteral = Util.invertLiteral(literal);
            if (clause2.contains(invertedLiteral))
                return literal;
        }
        return null;
    }

    /**
     * Picks a fitting proof node from <code>remainingClauses</code> to resolve
     * on the clause given in <code>tmpSubProofs</code>. The node is removed
     * from <code>remainingClauses</code> and added to <code>tmpSubProofs</code>
     * .
     * 
     * @param remainingClauses
     *            list of nodes to be searched for a resolving node.
     *            <em>Will be modified!</em>
     * @param tmpSubProofs
     *            list to add the found node to. Must have exactly one element
     *            first!
     * @param conclusions
     *            the literals that occur in the final conclusion, after all
     *            intermediate steps
     * @return the literal on which resolution is done, in arbitrary polarity.
     */
    private Formula pickAndUseFittingClause(
            List<VeritProofNode> remainingClauses,
            List<VeritProofNode> tmpSubProofs, Collection<Formula> conclusions) {
        assert (remainingClauses != null);
        assert (tmpSubProofs != null);
        assert (conclusions != null);
        assert (!remainingClauses.isEmpty());
        assert (tmpSubProofs.size() == 1);

        List<Formula> literals = tmpSubProofs.get(0).getLiteralConclusions()
                .editableCopy();
        literals.removeAll(conclusions);
        assert (!literals.isEmpty());
        for (Formula literal : literals) {
            for (int clauseCount = 0; clauseCount < remainingClauses.size(); clauseCount++) {
                Formula inverseLiteral = Util.invertLiteral(literal);
                if (remainingClauses.get(clauseCount).getLiteralConclusions()
                        .contains(inverseLiteral)) {
                    tmpSubProofs.add(remainingClauses.remove(clauseCount));
                    return literal;
                }
            }
        }
        // If we reach here, we found no clause to resolve with.
        // This should not happen.
        assert (false);
        return null;
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
        if (literalConclusions.isEmpty()) {
            List<Formula> list = new ArrayList<Formula>(1);
            list.add(PropositionalConstant.create(false));
            return OrFormula.generate(list);
        }
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
    public ImmutableSet<VeritProofNode> getParents() {
        assert (parents != null);
        return ImmutableSet.create(parents);
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
     * Removes the given <code>parent</code> from the list of parents. If the
     * given <code>parent</code> is not present in the current list of parents,
     * nothing happens.
     * 
     * @param parent
     *            the parent to remove
     */
    protected void removeParent(VeritProofNode parent) {
        if (parents.contains(parent)) {
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
        assert (this.subProofs.size() == 2);
        assert (this.type.equals(VeriTToken.RESOLUTION));

        if (!this.subProofs.contains(oldSubProof))
            return false;

        VeritProofNode otherSubProof = this.subProofs.get(0) == oldSubProof ? this.subProofs
                .get(1) : this.subProofs.get(0);
        for (Formula literal : oldSubProof.literalConclusions) {
            if (!newSubProof.literalConclusions.contains(literal)
                    && !otherSubProof.literalConclusions.contains(literal))
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
    @Deprecated
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

    /**
     * Creates a stronger (or equal) new node, and uses it instead of this one.
     * 
     * @param weakerSubProof
     *            the subproof for which a stronger counterpart can be used
     *            instead
     * @param strongerSubProof
     *            the stronger counterpart
     */
    protected void makeStronger(VeritProofNode weakerSubProof,
            VeritProofNode strongerSubProof) {
        assert (weakerSubProof != null);
        assert (strongerSubProof != null);
        assert (this.subProofs.size() == 2);
        assert (this.type.equals(VeriTToken.RESOLUTION));
        assert (this.subProofs.contains(weakerSubProof));
        assert (!this.subProofs.contains(strongerSubProof));
        assert (weakerSubProof.getLiteralConclusions()
                .containsAll(strongerSubProof.getLiteralConclusions()));
        assert (weakerSubProof.getLiteralConclusions().size() >= strongerSubProof
                .getLiteralConclusions().size());
        assert (this.parents.size() > 0 || this == this.proof.getRoot());

        if (strongerSubProof.literalConclusions.size() == 0) {
            this.proof.setNewRoot(strongerSubProof);
            return;
        }

        if (strongerSubProof.literalConclusions
                .containsAll(weakerSubProof.literalConclusions)
                && weakerSubProof.literalConclusions
                        .containsAll(strongerSubProof.literalConclusions)) {
            boolean updated = this.updateProofNode(weakerSubProof,
                    strongerSubProof);
            assert (updated);
            return;
        }

        Formula resolvingLiteral = this.findResolvingLiteral();
        if (!strongerSubProof.literalConclusions.contains(resolvingLiteral)
                && !strongerSubProof.literalConclusions.contains(Util
                        .invertLiteral(resolvingLiteral))) {
            assert (this.literalConclusions
                    .containsAll(strongerSubProof.literalConclusions));
            assert (this != this.proof.getRoot());
            // This resolution step is unnecessary. Make all parents stronger.
            for (VeritProofNode parent : this.parents) {
                parent.makeStronger(this, strongerSubProof);
            }
            return;
        }

        List<VeritProofNode> clauses = new ArrayList<VeritProofNode>();
        List<Formula> conclusions = new ArrayList<Formula>();
        for (VeritProofNode clause : this.subProofs) {
            if (clause.equals(weakerSubProof)) {
                clauses.add(strongerSubProof);
                for (Formula literal : strongerSubProof.literalConclusions) {
                    if (!conclusions.contains(literal))
                        conclusions.add(literal);
                }
            } else {
                clauses.add(clause);
                for (Formula literal : clause.literalConclusions) {
                    if (!conclusions.contains(literal))
                        conclusions.add(literal);
                }
            }
        }
        assert (clauses.size() == 2);
        conclusions.remove(resolvingLiteral);
        conclusions.remove(Util.invertLiteral(resolvingLiteral));

        if (this.literalConclusions.containsAll(conclusions)
                && conclusions.containsAll(this.literalConclusions)) {
            boolean updated = this.updateProofNode(weakerSubProof,
                    strongerSubProof);
            assert (updated);
            return;
        }

        assert (conclusions.size() < this.literalConclusions.size());
        assert (this.literalConclusions.containsAll(conclusions));

        // Do NOT do a cache lookup. Looking up stronger nodes likely results in
        // cycles!
        VeritProofNode strongerNode = new VeritProofNode("str_" + this.name,
                this.type, conclusions, clauses, null, this.proof);
        assert (strongerNode != null);

        for (VeritProofNode parent : this.parents) {
            parent.makeStronger(this, strongerNode);
        }
    }

    /**
     * 
     * @see java.lang.Object#toString()
     */
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
        str = str.replaceAll("\\s{2,}", " ").replace("\n", "");
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

        // Type specific tests

        if (this.type.equals(VeriTToken.INPUT)) {
            if (subProofs.size() != 0)
                return false;
            return true;
        }

        if (this.type.equals(VeriTToken.AND)) {
            // This type will be removed after parsing.
            // --> not detailed checks
            return true;
        }

        if (this.type.equals(VeriTToken.OR)) {
            // This type will be removed after parsing.
            // --> not detailed checks
            return true;
        }

        // Remaining types should have only literals in their conclusions

        for (Formula literal : literalConclusions) {
            if (!Util.isLiteral(literal))
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

        Set<Formula> literal1 = new HashSet<Formula>(subProofs.get(0)
                .getLiteralConclusionsAsSet());
        literal1.removeAll(literalConclusions);

        Set<Formula> literal2 = new HashSet<Formula>(subProofs.get(1)
                .getLiteralConclusionsAsSet());
        literal2.removeAll(literalConclusions);

        if (literal1.size() != 1 || literal2.size() != 1)
            return false;

        if (!Util.makeLiteralPositive(literal1.iterator().next()).equals(
                Util.makeLiteralPositive(literal2.iterator().next())))
            return false;
        if (!(Util.isNegativeLiteral(literal1.iterator().next()) ^ Util
                .isNegativeLiteral(literal2.iterator().next())))
            return false;

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
        Term[] terms = ((EqualityFormula) impliedLiteral).getTerms().toArray(
                new Term[0]);
        if (terms.length != 2)
            return false;

        Graph<Term, Formula> equalityGraph = new Graph<Term, Formula>();
        for (Formula literal : literalConclusions.subList(0,
                literalConclusions.size() - 1)) {
            if (!Util.isLiteral(literal))
                return false;
            if (!Util.isNegativeLiteral(literal))
                return false;
            if (!(Util.makeLiteralPositive(literal) instanceof EqualityFormula))
                return false;
            if (!((EqualityFormula) Util.makeLiteralPositive(literal))
                    .isEqual())
                return false;
            if (((EqualityFormula) Util.makeLiteralPositive(literal))
                    .getTerms().size() != 2)
                return false;

            Term[] currentTerms = ((EqualityFormula) Util
                    .makeLiteralPositive(literal)).getTerms().toArray(
                    new Term[0]);
            assert (currentTerms.length == 2);
            equalityGraph.addNode(currentTerms[0]);
            equalityGraph.addNode(currentTerms[1]);
            equalityGraph.addEdge(currentTerms[0], currentTerms[1], literal);
        }

        List<Formula> path = equalityGraph.findPath(terms[0], terms[1]);
        if (path == null) {
            if (!CongruenceClosure.checkVeritProofNode(this))
                return false;
        } else {

            assert (literalConclusions.containsAll(path));
            assert (path.size() == literalConclusions.size() - 1);
        }
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

        Term[] terms = ((EqualityFormula) impliedLiteral).getTerms().toArray(
                new Term[0]);

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

        if (terms1.size() > literalConclusions.size() - 1) // There can be more
                                                           // literals, due to
                                                           // replacement during
                                                           // cleaning.
            return false;

        // Taking the assumption that equalities in the axiom instantiation
        // occur in the same order as they occur as parameters to the
        // uninterpreted function
        for (int count = 0; count < terms1.size(); count++) {

            // For each parameter (-pair), search for negated equality.
            List<DomainTerm> eqTerms = new ArrayList<DomainTerm>(2);
            eqTerms.add(terms1.get(count));
            eqTerms.add(terms2.get(count));
            Formula literal;
            try {
                literal = EqualityFormula.create(eqTerms, true);
            } catch (IncomparableTermsException exc) {
                throw new RuntimeException(exc);
            }
            literal = NotFormula.create(literal);
            if (literalConclusions.contains(literal))
                continue;

            // Try other order of terms
            eqTerms.clear();
            eqTerms.add(terms2.get(count));
            eqTerms.add(terms1.get(count));
            try {
                literal = EqualityFormula.create(eqTerms, true);
            } catch (IncomparableTermsException exc) {
                throw new RuntimeException(exc);
            }
            literal = NotFormula.create(literal);
            if (literalConclusions.contains(literal))
                continue;

            // Try via transitivity chain
            Graph<Term, Formula> equalityGraph = new Graph<Term, Formula>();
            for (Formula currentLiteral : literalConclusions.subList(0,
                    literalConclusions.size() - 1)) {
                if (!Util.isLiteral(currentLiteral))
                    return false;
                if (!Util.isNegativeLiteral(currentLiteral))
                    return false;
                if (!(Util.makeLiteralPositive(currentLiteral) instanceof EqualityFormula))
                    return false;
                if (!((EqualityFormula) Util
                        .makeLiteralPositive(currentLiteral)).isEqual())
                    return false;
                if (((EqualityFormula) Util.makeLiteralPositive(currentLiteral))
                        .getTerms().size() != 2)
                    return false;

                Term[] currentTerms = ((EqualityFormula) Util
                        .makeLiteralPositive(currentLiteral)).getTerms()
                        .toArray(new Term[0]);
                assert (currentTerms.length == 2);
                equalityGraph.addNode(currentTerms[0]);
                equalityGraph.addNode(currentTerms[1]);
                equalityGraph.addEdge(currentTerms[0], currentTerms[1],
                        currentLiteral);
            }

            List<Formula> path = equalityGraph.findPath(terms1.get(count),
                    terms2.get(count));
            if (path != null) {
                assert (literalConclusions.containsAll(path));
                continue;
            }

            // Not found any matching equality.
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

        boolean badLiteralFound = false;
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
            if (Util.isBadLiteral(literal)) {
                if (badLiteralFound)
                    return false; // more than one bad literal found
                badLiteralFound = true;
            }
        }
        return badLiteralFound;
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
     * @return the list of good literals defining a bad one, or
     *         <code>null</code> if this node is not a good definition of a bad
     *         literal
     */
    public List<Formula> getDefiningGoodLiterals() {
        if (!isGoodDefinitionOfBadLiteral())
            return null;
        ArrayList<Formula> tmp = new ArrayList<Formula>();
        for (Formula literal : literalConclusions) {
            assert (Util.isLiteral(literal));
            if (!Util.isBadLiteral(literal))
                tmp.add(literal);
        }
        assert (!tmp.isEmpty());
        return tmp;
    }

    /**
     * @return the <code>proof</code>
     */
    public VeritProof getProof() {
        return proof;
    }

    /**
     * Checks whether this node resolves on the given <code>literal</code>.
     * 
     * @param literal
     *            must be a literal!
     * @return <code>true</code> if this node resolves on the given
     *         <code>literal</code>. <code>false</code> otherwise; in particular
     *         if this is not a resolution node.
     */
    public boolean resolvesOn(Formula literal) {
        assert (Util.isLiteral(literal));
        if (!this.type.equals(VeriTToken.RESOLUTION))
            return false;
        Formula resolvingLiteral = this.findResolvingLiteral();
        assert (Util.isLiteral(resolvingLiteral));
        assert (!Util.isNegativeLiteral(resolvingLiteral));
        return Util.makeLiteralPositive(literal).equals(resolvingLiteral);
    }

    /**
     * Only call on resolution nodes!
     * 
     * @return the resolving literal (in positive form)
     */
    public Formula findResolvingLiteral() {
        assert (checkResolution());
        Set<Formula> literal1 = new HashSet<Formula>(subProofs.get(0)
                .getLiteralConclusionsAsSet());
        literal1.removeAll(literalConclusions);
        return Util.makeLiteralPositive(literal1.iterator().next());
    }

    /**
     * If this node resolves on the given <code>literal</code>, returns the
     * child that has the literal in the opposite polarity as the given one.
     * 
     * @param literal
     * @return the child of this node which has the given literal in opposite
     *         polarity.
     */
    public VeritProofNode getChildWithLiteralInOppositePolarity(Formula literal) {
        assert (this.resolvesOn(literal));
        assert (subProofs.size() == 2);
        if (subProofs.get(0).getLiteralConclusionsAsSet().contains(literal)) {
            assert (subProofs.get(1).getLiteralConclusionsAsSet().contains(Util
                    .invertLiteral(literal)));
            return subProofs.get(1);
        }
        if (subProofs.get(1).getLiteralConclusionsAsSet().contains(literal)) {
            assert (subProofs.get(0).getLiteralConclusionsAsSet().contains(Util
                    .invertLiteral(literal)));
            return subProofs.get(0);
        }
        assert (false);
        return null;
    }

    /**
     * @return <code>true</code> if this is an axiom.
     */
    public boolean isAxiom() {
        if (type.equals(VeriTToken.EQ_CONGRUENT))
            return true;
        if (type.equals(VeriTToken.EQ_CONGRUENT_PRED))
            return true;
        if (type.equals(VeriTToken.EQ_REFLEXIVE))
            return true;
        if (type.equals(VeriTToken.EQ_TRANSITIVE))
            return true;

        return false;
    }

    /**
     * @return the partitions of the literals of this node.
     */
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> result = new HashSet<Integer>();
        for (Formula literal : literalConclusions)
            result.addAll(literal.getPartitionsFromSymbols());
        return result;
    }

    /**
     * @param path
     *            the path so far
     * @return <code>true</code> if no cycles are found
     */
    public boolean isAcyclic(List<VeritProofNode> path) {
        for (VeritProofNode child : subProofs) {
            if (path.contains(child))
                return false;
            path.add(child);
            if (!child.isAcyclic(path))
                return false;
            path.remove(path.size() - 1);
            assert (!path.contains(child));
        }
        return true;
    }
}
