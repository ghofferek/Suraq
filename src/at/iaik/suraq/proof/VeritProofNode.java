/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.IncomparableTermsException;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.DomainEq;
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
import at.iaik.suraq.util.MutableInteger;
import at.iaik.suraq.util.Util;
import at.iaik.suraq.util.chain.TransitivityCongruenceChain;
import at.iaik.suraq.util.graph.Graph;

/**
 * VeritProofSet is a single set-line in the proof. You shall not use this class
 * to create or modify the proof. Use VeritProof instead. To prevent you from
 * using certain functions, they are marked as deprecated.
 * 
 * @author chillebold
 * 
 */
public class VeritProofNode implements Serializable {

    private static final long serialVersionUID = 1L;

    private final int hashCode;

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
     * Used to disable printing of failure message while checking TRANS_CONGR
     * nodes.
     */
    private boolean suppressFailureMessage = false;

    /**
     * Stores suppressed messages
     */
    private String suppressedMessage = null;

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
        final boolean isTheoryLemma = CongruenceClosure
                .checkTheoryLemma(conclusions);
        List<Formula> reducedConclusions = new ArrayList<Formula>();
        for (Formula literal : conclusions) {
            if (!reducedConclusions.contains(literal))
                reducedConclusions.add(literal);
        }
        assert ((new HashSet<Formula>(reducedConclusions)).size() == reducedConclusions
                .size());

        List<VeritProofNode> tmpSubProofs = new ArrayList<VeritProofNode>(2);
        ArrayList<Formula> tmpLiteralConclusions = new ArrayList<Formula>();

        if (this.type.equals(VeriTToken.RESOLUTION) && clauses.size() > 2
                && !isTheoryLemma) {
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

                VeritProofNode intermediateNode = new VeritProofNode(name
                        + "_i" + count, VeriTToken.RESOLUTION,
                        tmpLiteralConclusions, tmpSubProofs, null, proof);
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

        if (isTheoryLemma) {
            this.subProofs = new ArrayList<VeritProofNode>(0);
            this.name = "lem." + name;
            this.type = VeriTToken.TRANS_CONGR;
        } else {
            this.subProofs = tmpSubProofs;
            this.name = name;
            this.type = type;
            for (VeritProofNode child : this.subProofs)
                child.addParent(this);
        }
        this.parents = new HashSet<VeritProofNode>(2);
        this.iargs = iargs == null ? null : new Integer(iargs);
        this.proof = proof;
        this.literalConclusions = new ImmutableArrayList<Formula>(
                tmpLiteralConclusions);

        assert (this.checkProofNode());
        assert (proof != null);
        proof.addProofNode(this);

        this.hashCode = literalConclusions.hashCode() + 32 * name.hashCode()
                + 64 * type.hashCode();
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
     * @return an immutable copy of the subproofs (might be empty)
     */
    public ImmutableArrayList<VeritProofNode> getSubProofs() {
        assert (subProofs != null);
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
        Set<VeritProofNode> newParents = new HashSet<VeritProofNode>();
        // Workaround because removal seems to be broken
        for (VeritProofNode otherParent : parents) {
            if (!parent.equals(otherParent))
                newParents.add(otherParent);
        }
        parents.clear();
        parents.addAll(newParents);
        // end workaround
        assert (!parents.contains(parent));
        if (parents.isEmpty())
            this.kill();
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
        // assert (oldSubProof.getParents().contains(this)); // Parent is
        // removed before update
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
        if (weakerSubProof == strongerSubProof)
            return;
        assert (weakerSubProof != strongerSubProof);
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

        if (subProofs != null) {
            if (subProofs.size() > 0) {
                str += "\nConclusions of subproofs:";
                for (VeritProofNode subproof : subProofs) {
                    str += "\n" + subproof.name + ": ";
                    for (Formula conclusion : subproof.literalConclusions) {
                        str += " "
                                + conclusion.toString()
                                        .replaceAll("\\s{2,}", " ")
                                        .replace("\n", "");
                    }
                }
            }
        }

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
                return failOnMessage("INPUT node with children");
            return true;
        }

        if (this.type.equals(VeriTToken.AND)) {
            // This type will be removed after parsing.
            // --> no detailed checks
            return true;
        }

        if (this.type.equals(VeriTToken.OR)) {
            // This type will be removed after parsing.
            // --> no detailed checks
            return true;
        }

        // Remaining types should have only literals in their conclusions

        for (Formula literal : literalConclusions) {
            if (!Util.isLiteral(literal))
                return failOnMessage("Non-literal in conclusion: "
                        + literal.toString());
        }

        if (this.type.equals(VeriTToken.EQ_REFLEXIVE)) {
            if (subProofs.size() != 0)
                return failOnMessage("Reflexivity node with children!");
            if (literalConclusions.size() != 1)
                return failOnMessage("Reflexivity node with more than one literal in conclusions!");
            assert (literalConclusions.size() == 1);
            Formula literal = literalConclusions.get(0);
            if (!Util.isReflexivity(literal))
                return failOnMessage("Not a correct reflexivity!");
            else
                return true;
        }

        if (this.type.equals(VeriTToken.EQ_CONGRUENT)) {
            return checkCongruence();
        }

        if (this.type.equals(VeriTToken.EQ_CONGRUENT_PRED)) {
            return checkCongruencePred();
        }

        if (this.type.equals(VeriTToken.EQ_TRANSITIVE)) {
            return checkTransitive();
        }

        if (this.type.equals(VeriTToken.RESOLUTION)) {
            return checkResolution();
        }

        if (this.type.equals(VeriTToken.TRANS_CONGR)) {
            this.suppressFailureMessage = true;
            boolean result = checkTransitive() || checkCongruence()
                    || checkCongruencePred();
            this.suppressFailureMessage = false;
            if (!result) {
                assert (suppressedMessage != null);
                System.out.println(suppressedMessage);
                suppressedMessage = null;
            }
            return result;
        }

        // unknown node type
        failOnMessage("Unknown node type!");
        assert (false);
        return false;
    }

    /**
     * Returns <code>false</code> and prints the given <code>message</code>,
     * unless it is <code>null</code>, in which case <code>true</code> is
     * returned and nothing is printed.
     * 
     * @param message
     *            the failure message to print.
     * @return <code>false</code> if <code>message != null</code>,
     *         <code>true</code> otherwise.
     */
    private boolean failOnMessage(String message) {
        if (message == null)
            return true;
        assert (message != null);
        StringBuffer messageBuffer = new StringBuffer();
        messageBuffer.append("ERROR: Check of node '" + this.name
                + "' failed.\n");
        messageBuffer.append(message);
        messageBuffer.append("\nNode data follows:\n");
        messageBuffer.append(this.toString());
        messageBuffer.append("\n");
        if (this.suppressFailureMessage) {
            suppressedMessage += messageBuffer.toString();
        } else
            System.out.println(messageBuffer.toString());

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
            return failOnMessage("Resolution with number of subproofs !=2. Number: "
                    + subProofs.size());

        // Special case if one of the two children is a "LEM instance" (a \/ ~a)
        if (subProofs.get(0).isLEM()) {
            Formula literal = Util
                    .makeLiteralPositive(subProofs.get(0).literalConclusions
                            .get(0));
            if (!subProofs.get(1).literalConclusions.contains(literal)
                    && !subProofs.get(1).literalConclusions.contains(Util
                            .invertLiteral(literal)))
                return failOnMessage("LEM literal not found in other subproof!");
            if (!literalConclusions
                    .containsAll(subProofs.get(1).literalConclusions))
                return failOnMessage("Missing a literal after LEM resolution.");
            if (!subProofs.get(1).literalConclusions
                    .containsAll(literalConclusions))
                return failOnMessage("Too much literals after LEM resolution.");
            return true;
        }

        if (subProofs.get(1).isLEM()) {
            Formula literal = Util
                    .makeLiteralPositive(subProofs.get(1).literalConclusions
                            .get(0));
            if (!subProofs.get(0).literalConclusions.contains(literal)
                    && !subProofs.get(0).literalConclusions.contains(Util
                            .invertLiteral(literal)))
                return failOnMessage("LEM literal not found in other subproof!");
            if (!literalConclusions
                    .containsAll(subProofs.get(0).literalConclusions))
                return failOnMessage("Missing a literal after LEM resolution.");
            if (subProofs.get(0).literalConclusions
                    .containsAll(literalConclusions))
                return failOnMessage("Too much literals after LEM resolution.");
            return true;
        }

        boolean resolvingLiteralFound = false;
        for (Formula literal : subProofs.get(0).literalConclusions) {
            if (!literalConclusions.contains(literal)
                    && !literalConclusions.contains(Util
                            .reverseTermsInLiteral(literal))) {
                if (resolvingLiteralFound)
                    return failOnMessage("Found more than one resolving literal!");
                Formula invertedLiteral = Util.invertLiteral(literal);
                if (!subProofs.get(1).literalConclusions
                        .contains(invertedLiteral))
                    return failOnMessage("Resolving literal "
                            + literal.toString().replaceAll("\\s{2,}", " ")
                                    .replace("\n", "")
                            + " from first subproof not found in inverse polarity in other subproof!");
                else
                    resolvingLiteralFound = true;
            }
        }
        if (!resolvingLiteralFound)
            return failOnMessage("No resolving literal found!");
        resolvingLiteralFound = false;
        for (Formula literal : subProofs.get(1).literalConclusions) {
            if (!literalConclusions.contains(literal)
                    && !literalConclusions.contains(Util
                            .reverseTermsInLiteral(literal))) {
                if (resolvingLiteralFound)
                    return failOnMessage("Found more than one resolving literal!");
                Formula invertedLiteral = Util.invertLiteral(literal);
                if (!subProofs.get(0).literalConclusions
                        .contains(invertedLiteral))
                    return failOnMessage("Resolving literal "
                            + literal.toString().replaceAll("\\s{2,}", " ")
                                    .replace("\n", "")
                            + " from second subproof not found in inverse polarity in other subproof!");
                else
                    resolvingLiteralFound = true;
            }
        }
        if (!resolvingLiteralFound)
            return failOnMessage("No resolving literal found!");
        for (Formula literal : literalConclusions) {
            if (!subProofs.get(0).literalConclusions.contains(literal)
                    && !subProofs.get(1).literalConclusions.contains(literal))
                return failOnMessage("Literal not originating from one of the subproofs found! Literal: "
                        + literal.toString());
        }

        Set<Formula> literal1 = new HashSet<Formula>(subProofs.get(0)
                .getLiteralConclusionsAsSet());
        literal1.removeAll(literalConclusions);

        Set<Formula> literal2 = new HashSet<Formula>(subProofs.get(1)
                .getLiteralConclusionsAsSet());
        literal2.removeAll(literalConclusions);

        if (literal1.size() != 1 || literal2.size() != 1)
            return failOnMessage("Conclusion misses at least one literal from subproofs!");

        if (!Util.makeLiteralPositive(literal1.iterator().next()).equals(
                Util.makeLiteralPositive(literal2.iterator().next())))
            return failOnMessage("Mismatch in resolving literal!");
        if (!(Util.isNegativeLiteral(literal1.iterator().next()) ^ Util
                .isNegativeLiteral(literal2.iterator().next())))
            return failOnMessage("Mismatch in resolving literal polarity!");

        return true;
    }

    /**
     * @return <code>true</code> iff this is an instance of the law of excluded
     *         middle (LEM).
     */
    private boolean isLEM() {
        if (literalConclusions.size() != 2)
            return false;
        assert (literalConclusions.size() == 2);
        Formula lit1 = literalConclusions.get(0);
        Formula lit2 = literalConclusions.get(1);
        if (Util.makeLiteralPositive(lit1).equals(
                Util.makeLiteralPositive(lit2))
                && (Util.getSignValue(lit1) ^ Util.getSignValue(lit2)))
            return true;
        return false;
    }

    /**
     * Call only on nodes with type <code>EQ_TRANSITIVE</code>.
     * 
     * @return <code>true</code> iff this is a valid transitivity axiom
     *         instantiation.
     */
    private boolean checkTransitive() {
        assert (this.type.equals(VeriTToken.EQ_TRANSITIVE) || this.type
                .equals(VeriTToken.TRANS_CONGR));
        if (literalConclusions.size() == 2) {
            if (!isLEM())
                return failOnMessage("Transitivity with size two that is not a LEM.");
            else
                return true;

        }
        if (literalConclusions.size() < 3)
            return failOnMessage("Transitivity axiom with less than 3 literals! Number: "
                    + literalConclusions.size());
        if (subProofs.size() != 0)
            return failOnMessage("Transitivity axiom with subproofs! Number: "
                    + subProofs.size());

        // Taking the assumption that the implied literal is the last one
        Formula impliedLiteral = literalConclusions.get(literalConclusions
                .size() - 1);
        if (Util.isNegativeLiteral(impliedLiteral))
            return failOnMessage("Implied literal is negative!");
        if (!(impliedLiteral instanceof EqualityFormula))
            return failOnMessage("Implied literal is not an equality!");
        if (!((EqualityFormula) impliedLiteral).isEqual())
            return failOnMessage("Implied literal is a disequality!");
        Term[] terms = ((EqualityFormula) impliedLiteral).getTerms().toArray(
                new Term[0]);
        if (terms.length != 2)
            return failOnMessage("Implied literal is equality with number of terms !=2.");

        Graph<Term, Formula> equalityGraph = new Graph<Term, Formula>();
        for (Formula literal : literalConclusions.subList(0,
                literalConclusions.size() - 1)) {
            if (!Util.isLiteral(literal))
                return failOnMessage("Found non-literal!");
            if (!Util.isNegativeLiteral(literal))
                return failOnMessage("Found unexpected positive literal!");
            if (!(Util.makeLiteralPositive(literal) instanceof EqualityFormula))
                return failOnMessage("Found unexpected non-equality literal!");
            if (!((EqualityFormula) Util.makeLiteralPositive(literal))
                    .isEqual())
                return failOnMessage("Found unexpected disequality!");
            if (((EqualityFormula) Util.makeLiteralPositive(literal))
                    .getTerms().size() != 2)
                return failOnMessage("Found equality literal with number of terms !=2.");

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
                return failOnMessage("Could not prove implied literal with congruence closure!");
        } else {

            assert (literalConclusions.containsAll(path));
        }
        return true;
    }

    /**
     * Call only on nodes with type <code>EQ_CONGRUENT_PRED</code>
     * 
     * @return <code>true</code>, iff this is a valid predicate congruence axiom
     *         instantiation.
     */
    private boolean checkCongruencePred() {
        assert (this.type.equals(VeriTToken.EQ_CONGRUENT_PRED) || this.type
                .equals(VeriTToken.TRANS_CONGR));

        if (literalConclusions.size() < 3)
            return failOnMessage("Less than 3 literals in predicate congruence axiom! Number: "
                    + literalConclusions.size());
        if (subProofs.size() != 0)
            return failOnMessage("Predicate congruence axiom with subproofs! Number: "
                    + subProofs.size());

        // Taking the assumption that the "implied literal" is the last one.
        Formula impliedLiteral = literalConclusions.get(literalConclusions
                .size() - 1);

        // Taking the assumption that the second-to-last literal is also
        // a predicate instance, with inverse polarity
        Formula inversePredicateLiteral = literalConclusions
                .get(literalConclusions.size() - 2);

        if (!(Util.makeLiteralPositive(impliedLiteral) instanceof UninterpretedPredicateInstance))
            return failOnMessage("Implied literal not a predicate instance!");

        if (!(Util.makeLiteralPositive(inversePredicateLiteral) instanceof UninterpretedPredicateInstance))
            return failOnMessage("The literal expected to be the inverse predicate instance is not a predicate instance!");

        if (Util.getSignValue(impliedLiteral) == Util
                .getSignValue(inversePredicateLiteral))
            return failOnMessage("Implied literal and inverse predicate literal have the same polarity!");

        UninterpretedPredicateInstance instance1 = (UninterpretedPredicateInstance) Util
                .makeLiteralPositive(impliedLiteral);
        UninterpretedPredicateInstance instance2 = (UninterpretedPredicateInstance) Util
                .makeLiteralPositive(inversePredicateLiteral);

        if (!instance1.getFunction().equals(instance2.getFunction()))
            return failOnMessage("Predicate mismatch!");

        List<DomainTerm> terms1 = instance1.getParameters();
        List<DomainTerm> terms2 = instance2.getParameters();
        assert (terms1.size() == terms2.size());

        // Check that there is an equality-chain for each parameter
        for (int count = 0; count < terms1.size(); count++) {
            // Try via transitivity chain
            Graph<Term, Formula> equalityGraph = new Graph<Term, Formula>();
            for (Formula currentLiteral : literalConclusions.subList(0,
                    literalConclusions.size() - 2)) {
                if (!Util.isLiteral(currentLiteral))
                    return failOnMessage("Found a non-literal!");
                if (!Util.isNegativeLiteral(currentLiteral))
                    return failOnMessage("Found an unexpected non-negative literal!");
                if (!(Util.makeLiteralPositive(currentLiteral) instanceof EqualityFormula))
                    return failOnMessage("Found an unexpected non-equality literal!");
                if (!((EqualityFormula) Util
                        .makeLiteralPositive(currentLiteral)).isEqual())
                    return failOnMessage("Found an unexpected disequality!");
                if (((EqualityFormula) Util.makeLiteralPositive(currentLiteral))
                        .getTerms().size() != 2)
                    return failOnMessage("Found an equality with number of terms !=2.");

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

            // Try finding something with Congruence Closure
            List<EqualityFormula> ccLiterals = new ArrayList<EqualityFormula>();
            for (Formula literal : literalConclusions.subList(0,
                    literalConclusions.size() - 2)) {
                assert (Util.makeLiteralPositive(literal) instanceof EqualityFormula);
                ccLiterals.add((EqualityFormula) Util
                        .makeLiteralPositive(literal));
            }
            if (CongruenceClosure.checkLiteralImplication(ccLiterals,
                    terms1.get(count), terms2.get(count)))
                continue;

            // Congruence Closure did not work either
            return failOnMessage("Did not find an equality path for parameter number "
                    + count);
        }

        return true;
    }

    /**
     * Call only on nodes with type <code>EQ_CONGRUENT</code>
     * 
     * @return <code>true</code>, iff this is a valid congruence axiom
     *         instantiation.
     */
    private boolean checkCongruence() {
        assert (this.type.equals(VeriTToken.EQ_CONGRUENT) || this.type
                .equals(VeriTToken.TRANS_CONGR));

        if (literalConclusions.size() < 2)
            return failOnMessage("Too few conclusion literals: "
                    + literalConclusions.size());
        if (subProofs.size() != 0)
            return failOnMessage("Subproofs non-empty! Size: "
                    + subProofs.size());

        // Taking the assumption that the "implied literal" is the last one.
        Formula impliedLiteral = literalConclusions.get(literalConclusions
                .size() - 1);
        if (Util.isNegativeLiteral(impliedLiteral))
            return failOnMessage("Implied literal is negative!");

        if (!(impliedLiteral instanceof EqualityFormula))
            return failOnMessage("Implied literal in congruence axiom is not an equality!");

        if (!((EqualityFormula) impliedLiteral).isEqual())
            return failOnMessage("Implied literal in congruence axiom is a disequality!");

        Term[] terms = ((EqualityFormula) impliedLiteral).getTerms().toArray(
                new Term[0]);

        if (terms.length != 2)
            return false;

        List<DomainTerm> terms1 = null;
        List<DomainTerm> terms2 = null;

        if (terms[0] instanceof UninterpretedFunctionInstance) {
            if (!(terms[1] instanceof UninterpretedFunctionInstance))
                return failOnMessage("Second equality term is not an uninterpreted function instance!");
            terms1 = ((UninterpretedFunctionInstance) terms[0]).getParameters();
            terms2 = ((UninterpretedFunctionInstance) terms[1]).getParameters();
            assert (terms1 != null);
            assert (terms2 != null);
            if (terms1.size() != terms2.size())
                return failOnMessage("Implied literal has uninterpreted function instances with different number of parameters");
            if (!((UninterpretedFunctionInstance) terms[0]).getFunction()
                    .equals(((UninterpretedFunctionInstance) terms[1])
                            .getFunction()))
                return failOnMessage("Implied literal has non-matching uninterpreted function instances!");
        } else {
            return failOnMessage("First equality term is not an uninterpreted function instance!");
        }

        assert (terms1 != null);
        assert (terms2 != null);
        assert (terms1.size() == terms2.size());

        if (terms1.size() > literalConclusions.size() - 1) // There can be more
                                                           // literals, due to
                                                           // replacement during
                                                           // cleaning.
            return failOnMessage("Not enough literals for congruence!");

        // Taking the assumption that equalities in the axiom instantiation
        // occur in the same order as they occur as parameters to the
        // uninterpreted function
        boolean allOk = true;
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
            allOk = true;
            for (Formula currentLiteral : literalConclusions.subList(0,
                    literalConclusions.size() - 1)) {
                if (!Util.isLiteral(currentLiteral))
                    return failOnMessage("Non-Literal found!");
                if (!Util.isNegativeLiteral(currentLiteral))
                    return failOnMessage("Unexpected non-negative literal found!");
                if (!(Util.makeLiteralPositive(currentLiteral) instanceof EqualityFormula))
                    return failOnMessage("Non-equality literal found!");
                if (!((EqualityFormula) Util
                        .makeLiteralPositive(currentLiteral)).isEqual())
                    return failOnMessage("Disequality-literal found!");
                if (((EqualityFormula) Util.makeLiteralPositive(currentLiteral))
                        .getTerms().size() != 2)
                    return failOnMessage("Equality with number of terms !=2 found!");

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

            // Not found any matching equality. Try with Congruence Closure
            // instead, as the graph does not merge congruences automatically
            allOk = false;
            break;

        }
        if (!allOk) { // check with Congruence Closure
            List<EqualityFormula> positiveLiterals = new ArrayList<EqualityFormula>(
                    literalConclusions.size() - 1);
            for (Formula literal : literalConclusions.subList(0,
                    literalConclusions.size() - 1)) {
                assert (Util.makeLiteralPositive(literal) instanceof EqualityFormula);
                positiveLiterals.add((EqualityFormula) Util
                        .makeLiteralPositive(literal));
            }
            assert (impliedLiteral instanceof DomainEq);
            if (!CongruenceClosure.checkLiteralImplication(positiveLiterals,
                    (DomainEq) impliedLiteral))
                return failOnMessage("Could not prove congruence axiom with congruence closure.");
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
     * Checks whether this is a theory axiom, based solely on the type of the
     * node.
     * 
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
        if (type.equals(VeriTToken.TRANS_CONGR))
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
     * @param notPartOfCycle
     *            a set of nodes which are not part of a cycle.
     * @return <code>true</code> if no cycles are found
     */
    public boolean isAcyclic(List<VeritProofNode> path,
            Set<VeritProofNode> notPartOfCycle,
            MutableInteger lastReportedPercentage) {

        int percentage = (int) Math
                .floor(((double) notPartOfCycle.size() / proof.size()) * 100);
        if (percentage >= lastReportedPercentage.intValue() + 10) {
            Util.printToSystemOutWithWallClockTimePrefix("Done " + percentage
                    + "% of nodes during acyclicity check.");
            lastReportedPercentage.add(10);
        }
        for (VeritProofNode child : subProofs) {
            if (path.contains(child))
                return false;
            if (notPartOfCycle.contains(child))
                continue;
            path.add(child);
            if (!child.isAcyclic(path, notPartOfCycle, lastReportedPercentage))
                return false;
            path.remove(path.size() - 1);
            assert (!path.contains(child));
        }
        notPartOfCycle.add(this);
        return true;
    }

    /**
     * Splits a predicate congruence that belongs to more than one partition.
     * This method (presently) only support unary predicates!
     * 
     * @return a replacement for this leaf.
     */
    public VeritProofNode splitPredicateLeaf() {

        assert (this.type.equals(VeriTToken.EQ_CONGRUENT_PRED));
        assert (this.checkCongruencePred());

        // Here, the last literal can also be negative.
        assert (Util
                .isAtom(literalConclusions.get(literalConclusions.size() - 1)) ^ Util
                .isAtom(literalConclusions.get(literalConclusions.size() - 2)));
        int posIndex = Util.isAtom(literalConclusions.get(literalConclusions
                .size() - 1)) ? literalConclusions.size() - 1
                : literalConclusions.size() - 2;
        int negIndex = posIndex == literalConclusions.size() - 1 ? posIndex - 1
                : posIndex + 1;
        UninterpretedPredicateInstance impliedLiteral = (UninterpretedPredicateInstance) literalConclusions
                .get(posIndex);
        UninterpretedPredicateInstance inversePredicateLiteral = (UninterpretedPredicateInstance) Util
                .makeLiteralPositive(literalConclusions.get(negIndex));

        // FIXME this method presently only support unary predicates!
        if (impliedLiteral.getParameters().size() != 1
                || inversePredicateLiteral.getParameters().size() != 1) {
            Util.printToSystemOutWithWallClockTimePrefix("ERROR: Cannot split the following leaf:");
            System.out.println(this.toString());
            Util.printToSystemOutWithWallClockTimePrefix("Only unary predicates supported by current implementation!");
            throw new RuntimeException(
                    "Non-unary predicate congruence in need of splitting detected.");
        }

        DomainTerm term1 = inversePredicateLiteral.getParameters().get(0);
        DomainTerm term2 = impliedLiteral.getParameters().get(0);
        List<DomainTerm> terms = new ArrayList<DomainTerm>(2);
        terms.add(term1);
        terms.add(term2);
        DomainEq equality = DomainEq.create(terms, true);

        List<DomainEq> otherLiterals = new ArrayList<DomainEq>(
                literalConclusions.size() - 2);
        for (int count = 0; count < literalConclusions.size() - 2; count++) {
            assert (Util.isLiteral(literalConclusions.get(count)));
            assert (Util.isNegativeLiteral(literalConclusions.get(count)));
            assert (Util.makeLiteralPositive(literalConclusions.get(count)) instanceof DomainEq);
            otherLiterals.add((DomainEq) Util
                    .makeLiteralPositive(literalConclusions.get(count)));
        }

        TransitivityCongruenceChain chain1 = TransitivityCongruenceChain
                .create(equality, otherLiterals, this);
        TransitivityCongruenceChain chain2 = chain1.splitAtGlobalTerm();

        DomainTerm globalTerm = chain2.getStart().getTerm();
        assert (globalTerm.getPartitionsFromSymbols().size() == 1);
        assert (globalTerm.getPartitionsFromSymbols().iterator().next()
                .equals(-1));
        UninterpretedPredicateInstance globalInstancePositive;
        try {
            globalInstancePositive = UninterpretedPredicateInstance.create(
                    impliedLiteral.getFunction(), globalTerm);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected exception while constructing UninterpretedPredicateInstance.",
                    exc);
        }
        NotFormula globalInstanceNegative = NotFormula
                .create(globalInstancePositive);

        List<Formula> literals1 = new ArrayList<Formula>();
        List<DomainTerm> terms1 = new ArrayList<DomainTerm>(2);
        terms1.add(term1);
        terms1.add(globalTerm);
        DomainEq equality1 = DomainEq.create(terms1, true);
        NotFormula disequality1 = NotFormula.create(equality1);
        literals1.add(disequality1);
        literals1.add(NotFormula.create(inversePredicateLiteral));
        literals1.add(globalInstancePositive);
        VeritProofNode predicateNode1 = new VeritProofNode(
                "pred1_" + this.name, VeriTToken.EQ_CONGRUENT_PRED, literals1,
                null, null, this.proof);
        VeritProofNode chain1Node = chain1.toColorableProof();
        List<VeritProofNode> leftSubProofs = new ArrayList<VeritProofNode>(2);
        leftSubProofs.add(chain1Node);
        leftSubProofs.add(predicateNode1);
        List<Formula> literalsLeft = new ArrayList<Formula>(
                chain1Node.getLiteralConclusions());
        literalsLeft.remove(literalsLeft.size() - 1);
        literalsLeft.add(NotFormula.create(inversePredicateLiteral));
        literalsLeft.add(globalInstancePositive);
        VeritProofNode left = new VeritProofNode("predLeft_" + this.name,
                VeriTToken.RESOLUTION, literalsLeft, leftSubProofs, null,
                this.proof);

        List<Formula> literals2 = new ArrayList<Formula>();
        List<DomainTerm> terms2 = new ArrayList<DomainTerm>(2);
        terms2.add(globalTerm);
        terms2.add(term2);
        DomainEq equality2 = DomainEq.create(terms2, true);
        NotFormula disequality2 = NotFormula.create(equality2);
        literals2.add(disequality2);
        literals2.add(globalInstanceNegative);
        literals2.add(impliedLiteral);
        VeritProofNode predicateNode2 = new VeritProofNode(
                "pred2_" + this.name, VeriTToken.EQ_CONGRUENT_PRED, literals2,
                null, null, this.proof);
        VeritProofNode chain2Node = chain2.toColorableProof();
        List<VeritProofNode> rightSubProofs = new ArrayList<VeritProofNode>(2);
        rightSubProofs.add(chain2Node);
        rightSubProofs.add(predicateNode2);
        List<Formula> literalsRight = new ArrayList<Formula>(
                chain2Node.getLiteralConclusions());
        literalsRight.remove(literalsRight.size() - 1);
        literalsRight.add(globalInstanceNegative);
        literalsRight.add(impliedLiteral);
        VeritProofNode right = new VeritProofNode("predRight_" + this.name,
                VeriTToken.RESOLUTION, literalsRight, rightSubProofs, null,
                this.proof);

        List<Formula> resultLiterals = new ArrayList<Formula>();
        resultLiterals.addAll(left.getLiteralConclusions());
        resultLiterals.addAll(right.getLiteralConclusions());
        resultLiterals.remove(globalInstanceNegative);
        resultLiterals.remove(globalInstancePositive);
        List<VeritProofNode> resultSubProofs = new ArrayList<VeritProofNode>(2);
        resultSubProofs.add(left);
        resultSubProofs.add(right);
        VeritProofNode result = new VeritProofNode("predResult_" + this.name,
                VeriTToken.RESOLUTION, resultLiterals, resultSubProofs, null,
                this.proof);

        return result;
    }

    /**
     * @return <code>true</code> iff this node has symbols from no more than one
     *         partition.
     */
    public boolean isColorable() {
        Set<Integer> partitions = this.getPartitionsFromSymbols();
        partitions.remove(-1);
        return partitions.size() <= 1;
    }

    /**
     * Recursively replaces the given <code>inverseBadLiteral</code> in this
     * subtree and returns new nodes where it has been replaced by the
     * <code>definingLiterals</code> instead.
     * 
     * @param inverseBadLiteral
     *            the literal to replace
     * @param definingLiterals
     *            the defining literals to put in instead
     * @param dagOperationCache
     *            a cache for not unwinding the DAG.
     * @return a new node in whose subtree <code>inverseBadLiteral</code> does
     *         not occur any more
     */
    protected VeritProofNode replaceInverseBadLiteral(
            Formula inverseBadLiteral, List<Formula> definingLiterals,
            Map<VeritProofNode, VeritProofNode> dagOperationCache) {
        assert (inverseBadLiteral != null);
        assert (definingLiterals != null);
        assert (dagOperationCache != null);

        VeritProofNode result = dagOperationCache.get(this);
        if (result != null)
            return result;

        assert (this.literalConclusions.contains(inverseBadLiteral) || this.subProofs
                .size() == 2);

        // Recursive Calls
        List<VeritProofNode> newSubProofs = null;
        if (this.subProofs.size() != 0) {
            assert (this.subProofs.size() == 2);
            assert (this.type.equals(VeriTToken.RESOLUTION));
            newSubProofs = new ArrayList<VeritProofNode>(2);
            for (VeritProofNode subProof : this.subProofs) {
                if (subProof.literalConclusions.contains(inverseBadLiteral))
                    newSubProofs.add(subProof.replaceInverseBadLiteral(
                            inverseBadLiteral, definingLiterals,
                            dagOperationCache));
                else
                    newSubProofs.add(subProof);
            }

            // If this node resolves one of the defining literals, this literal
            // should not be reintroduced into any nodes that are below (i.e.,
            // closer to the root as) this node.
            Formula resolvingLiteral = Util.findResolvingLiteral(newSubProofs);
            assert (resolvingLiteral != null);
            definingLiterals.remove(resolvingLiteral);
            definingLiterals.remove(Util.invertLiteral(resolvingLiteral));
        }

        // Prepare new node contents
        String newName = proof.freshNodeName("repl", this.name);
        List<Formula> newConclusions = new ArrayList<Formula>(
                this.literalConclusions.size());
        for (Formula literal : this.literalConclusions) {
            if (literal.equals(inverseBadLiteral)) {
                for (Formula definingLiteral : definingLiterals) {
                    if (!newConclusions.contains(definingLiteral))
                        newConclusions.add(definingLiteral);
                }
            } else {
                if (!newConclusions.contains(literal))
                    newConclusions.add(literal);
            }
        }
        assert (!newConclusions.contains(inverseBadLiteral));

        result = this.proof.addProofNode(newName, this.type, newConclusions,
                newSubProofs, null);
        dagOperationCache.put(this, result);
        return result;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return hashCode;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof VeritProofNode))
            return false;

        final VeritProofNode other = (VeritProofNode) obj;
        if (this.hashCode != other.hashCode)
            return false;
        if (this.proof != other.proof)
            return false;
        if (!this.name.equals(other.name))
            return false;
        if (!this.type.equals(other.type))
            return false;
        if (!(this.iargs == null ? other.iargs == null : this.iargs
                .equals(other.iargs)))
            return false;
        if (!(this.subProofs == null ? other.subProofs == null : this.subProofs
                .equals(other.subProofs)))
            return false;
        if (!(this.parents == null ? other.parents == null : this.parents
                .equals(other.parents)))
            return false;
        return true;
    }

}
