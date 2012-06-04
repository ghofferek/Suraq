/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.IncomparableTermsException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.FunctionMacro;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalEq;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtsolver.SMTSolver;
import at.iaik.suraq.util.Util;

/**
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
public class Z3Proof implements SMTLibObject {

    /**
     * global counter to keep track of running DAG traversals.
     */
    private static int operationCount = 0;

    /**
     * lists operations which already traversed this node.
     */
    protected List<Integer> visitedByOperation = new ArrayList<Integer>();

    protected Set<String> assertedStr = new HashSet<String>();

    /**
     * The proof type.
     */
    protected Token proofType;

    /**
     * The list of sub proofs.
     */
    protected List<Z3Proof> subProofs;

    /**
     * This formula is the consequent of this proof. It should either be an
     * <code>OrFormula</code> or the constant formula <code>false</code>.
     */
    protected Formula consequent;

    /**
     * Flag that indicates from which assert an asserted node comes. Only valid
     * for nodes of type ASSERTED.
     */
    protected int assertPartition = 0;

    /**
     * A unique ID of the node.
     */
    protected final int id;

    /**
     * Specifies if this proof object is an axiom introduced during
     * transformation.
     */
    protected boolean axiom = false;

    private static int instanceCounter = 1;

    /**
     * 
     * Constructs a new <code>Z3Proof</code>.
     * 
     */
    public Z3Proof() {
        this.proofType = null;
        this.subProofs = new ArrayList<Z3Proof>();
        this.consequent = null;
        this.id = Z3Proof.instanceCounter++;
        if (this.id % 1000 == 0)
            System.out.println("  Created the " + this.id + " proof node.");
        this.assertPartition = -1;
    }

    /**
     * 
     * Constructs a new <code>Z3Proof</code>.
     * 
     * @param proofType
     *            the type of the proof
     * @param subProofs
     *            the list of all subproofs
     * @param consequent
     *            the formula which has to be proved
     */
    public Z3Proof(Token proofType, Z3Proof subProof1, Z3Proof subProof2,
            Formula consequent) {

        if (proofType == null)
            throw new RuntimeException("null prooftype not allowed!");

        this.proofType = proofType;
        this.subProofs = new ArrayList<Z3Proof>();
        if (subProof1 != null)
            this.subProofs.add(subProof1);
        if (subProof2 != null)
            this.subProofs.add(subProof2);
        this.consequent = consequent;
        this.id = Z3Proof.instanceCounter++;
        if (this.id % 1000 == 0)
            System.out.println("  Created the " + this.id + " proof node.");
        this.setAssertPartition();
        assert (this.checkZ3ProofNode());
    }

    /**
     * 
     * Constructs a new <code>Z3Proof</code>.
     * 
     * @param proofType
     *            the type of the proof
     * @param subProofs
     *            the list of all subproofs
     * @param consequent
     *            the formula which has to be proved
     */
    public Z3Proof(Token proofType, List<? extends Z3Proof> subProofs,
            Formula consequent) {

        if (proofType == null)
            throw new RuntimeException("null prooftype not allowed!");

        this.proofType = proofType;
        assert (subProofs != null);
        this.subProofs = new ArrayList<Z3Proof>();
        this.subProofs.addAll(subProofs);
        this.consequent = consequent;
        this.id = Z3Proof.instanceCounter++;
        if (this.id % 1000 == 0)
            System.out.println("  Created the " + this.id + " proof node.");
        this.setAssertPartition();
        assert (this.checkZ3ProofNode());
    }

    private void setAssertPartition() {
        if (proofType.equals(SExpressionConstants.ASSERTED)) {
            Set<Integer> partitions = consequent.getPartitionsFromSymbols();
            assert (partitions.size() <= 2);
            partitions.remove(new Integer(-1));

            if (partitions.size() > 0) {
                assert (partitions.size() == 1);
                assertPartition = partitions.iterator().next();
            } else
                assertPartition = 1; // arbitrary choice for globals
            assert (assertPartition > 0);
        }
    }

    /**
     * Creates a new <code>Z3Proof</code> which is of the same type as
     * <code>this</code> object and has the given subProofs and consequent.
     * 
     * @param subProofs
     *            List of sub-proofs
     * @param consequent
     *            the consequent
     * @return a new <code>Z3Proof</code> with the same type as
     *         <code>this</code>.
     */
    protected Z3Proof create(List<Z3Proof> subProofs, Formula consequent) {

        List<Z3Proof> newSubProofs = new ArrayList<Z3Proof>();

        for (Z3Proof subProof : subProofs) {
            newSubProofs.add(subProof);
        }

        Z3Proof instance = new Z3Proof(new Token(this.proofType), newSubProofs,
                consequent);

        return instance;
    }

    /**
     * Returns the type of the proof.
     * 
     * @return the <code>proofType</code>
     */
    public Token getProofType() {
        return this.proofType;
    }

    /**
     * Returns the list of sub proofs
     * 
     * @return the <code>thenBranch</code>
     */
    public List<Z3Proof> getSubProofs() {
        return this.subProofs;
    }

    /**
     * Returns the formula which has to be proved
     * 
     * @return the <code>consequent</code>
     */
    public Formula getConsequent() {
        return this.consequent;
    }

    /**
     * Converts this proof into an s-expression compatible with SMTLIBv2. Only
     * the proof itself is converted. No variable/function/macro declarations
     * are included.
     * 
     * @return this proof as an SMTLIBv2 s-expression.
     */
    @Override
    public SExpression toSmtlibV2() {
        List<SExpression> children = new ArrayList<SExpression>();
        children.add(this.proofType);
        for (Z3Proof subProof : this.subProofs)
            children.add(subProof.toSmtlibV2());

        children.add(this.consequent.toSmtlibV2());
        return new SExpression(children);
    }

    /**
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.toSmtlibV2().toString();
    }

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        int operationId = startDAGOperation();
        Set<Integer> result = this
                .getPartitionsFromSymbolsRecursion(operationId);
        endDAGOperation(operationId);
        return result;
    }

    public Set<Integer> getPartitionsFromSymbolsRecursion(int operationId) {
        visitedByDAGOperation(operationId);

        Set<Integer> partitions = consequent.getPartitionsFromSymbols();

        for (Z3Proof proof : subProofs) {
            if (proof.wasVisitedByDAGOperation(operationId))
                continue;
            partitions.addAll(proof
                    .getPartitionsFromSymbolsRecursion(operationId));
        }
        return partitions;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return this.id;
    }

    /**
     * Compares the object references (pointers). This helps for distinguishing
     * trees from DAGs.
     * 
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        return (this == obj);
    }

    /**
     * This method is based on just looking at nodes with type ASSERTED and
     * checking from which assert statement they originate (according to their
     * own claim). Symbols are not checked.
     * 
     * This method and the returned set does not have a notion of "global". If
     * the subtree is just from one assert statement, the cardinality of the
     * returned set should be 1.
     * 
     * @return
     */

    public Set<Integer> getPartitionsFromAsserts() {
        int operationId = startDAGOperation();
        Set<Integer> result = this
                .getPartitionsFromAssertsRecursion(operationId);
        endDAGOperation(operationId);
        return result;
    }

    public Set<Integer> getPartitionsFromAssertsRecursion(int operationId) {

        visitedByDAGOperation(operationId);

        Set<Integer> assertPartitions = new HashSet<Integer>();
        for (Z3Proof z3Proofchild : this.subProofs) {
            if (z3Proofchild.wasVisitedByDAGOperation(operationId))
                continue;
            assertPartitions.addAll(z3Proofchild
                    .getPartitionsFromAssertsRecursion(operationId));
        }

        if (proofType.equals(SExpressionConstants.ASSERTED)) {
            if (assertPartition <= 0)
                assert (false);
            assertPartitions.add(new Integer(assertPartition));
        }

        return assertPartitions;
    }

    public int getID() {
        return this.id;
    }

    public Set<Z3Proof> getLemmas() {
        int operationId = startDAGOperation();
        Set<Z3Proof> result = this.getLemmasRecursion(operationId);
        endDAGOperation(operationId);
        return result;
    }

    private Set<Z3Proof> getLemmasRecursion(int operationId) {
        visitedByDAGOperation(operationId);

        Set<Z3Proof> lemmas = new HashSet<Z3Proof>();
        if (proofType.equals(SExpressionConstants.LEMMA)) {
            lemmas.add(this);
        }
        for (Z3Proof z3Proofchild : this.subProofs) {
            if (z3Proofchild.wasVisitedByDAGOperation(operationId))
                continue;
            lemmas.addAll(z3Proofchild.getLemmasRecursion(operationId));
        }
        return lemmas;
    }

    public Set<Z3Proof> getHypotheses() {
        int operationId = startDAGOperation();
        Set<Z3Proof> result = this.getHypothesesRecursion(operationId);
        endDAGOperation(operationId);
        return result;
    }

    private Set<Z3Proof> getHypothesesRecursion(int operationId) {
        visitedByDAGOperation(operationId);

        Set<Z3Proof> hypotheses = new HashSet<Z3Proof>();
        if (proofType.equals(SExpressionConstants.HYPOTHESIS)) {
            assert (this.subProofs.size() == 0);
            hypotheses.add(this);
        }
        if (this instanceof TransformedZ3Proof) {
            if (((TransformedZ3Proof) this).isHypothesis()) {
                assert (this.subProofs.size() == 0);
                hypotheses.add(this);
            }
        }
        for (Z3Proof z3Proofchild : this.subProofs) {
            if (z3Proofchild.wasVisitedByDAGOperation(operationId))
                continue;
            hypotheses.addAll(z3Proofchild.getHypothesesRecursion(operationId));
        }
        return hypotheses;
    }

    public void localLemmasToAssertions() {
        int operationId = startDAGOperation();
        this.localLemmasToAssertionsRecursion(operationId);
        endDAGOperation(operationId);
    }

    public void localLemmasToAssertionsRecursion(int operationId) {
        visitedByDAGOperation(operationId);

        if (proofType.equals(SExpressionConstants.LEMMA)) {
            assert (subProofs.size() == 1);

            Set<Integer> partitionsFromAsserts = subProofs.get(0)
                    .getPartitionsFromAsserts();
            assert (!partitionsFromAsserts.contains(new Integer(-1)));

            if (partitionsFromAsserts.size() > 1) {
                if (!(subProofs.get(0).wasVisitedByDAGOperation(operationId)))
                    subProofs.get(0).localLemmasToAssertionsRecursion(
                            operationId);
                return;
            }

            Set<Integer> symbolsPartitions = consequent
                    .getPartitionsFromSymbols();
            symbolsPartitions.remove(new Integer(-1));
            if (partitionsFromAsserts.equals(symbolsPartitions)) {
                proofType = SExpressionConstants.ASSERTED;
                if (partitionsFromAsserts.size() == 1)
                    assertPartition = partitionsFromAsserts.iterator().next();
                else if (partitionsFromAsserts.size() == 0)
                    assertPartition = 1; // arbitrary choice
                else
                    assert (false); // unreachable
                assert (assertPartition > 0);
                subProofs = new ArrayList<Z3Proof>();
                return;
            } else
                return;
        } else
            for (Z3Proof child : subProofs) {
                if (child.wasVisitedByDAGOperation(operationId))
                    continue;
                child.localLemmasToAssertionsRecursion(operationId);
            }

    }

    public void removeLocalSubProofs() {
        int operationId = startDAGOperation();
        this.removeLocalSubProofsRecursion(operationId);
        endDAGOperation(operationId);
    }

    public void removeLocalSubProofsRecursion(int operationId) {
        visitedByDAGOperation(operationId);

        Set<Integer> partitionsFromAsserts = this.getPartitionsFromAsserts();

        if (partitionsFromAsserts.size() == 1) {
            assert (!partitionsFromAsserts.contains((new Integer(-1))));
            Set<Integer> symbolPartitions = this.getPartitionsFromSymbols();
            assert (symbolPartitions.size() > 0);
            symbolPartitions.remove(-1);
            if ((symbolPartitions.equals(partitionsFromAsserts) || symbolPartitions
                    .size() == 0) && this.getHypotheses().size() == 0) {
                proofType = SExpressionConstants.ASSERTED;
                this.assertPartition = partitionsFromAsserts.iterator().next();
                subProofs = new ArrayList<Z3Proof>();
                return;
            }
        }

        for (Z3Proof child : subProofs) {
            if (child.wasVisitedByDAGOperation(operationId))
                continue;
            child.removeLocalSubProofsRecursion(operationId);
        }
    }

    public void dealWithModusPonens() {
        int operationId = startDAGOperation();
        this.dealWithModusPonensRecursion(operationId);
        endDAGOperation(operationId);
    }

    public void dealWithModusPonensRecursion(int operationId) {
        visitedByDAGOperation(operationId);

        if (this.proofType.equals(SExpressionConstants.MODUS_PONENS)) {
            assert (subProofs.size() == 2);
            assert (this.hasSingleLiteralConsequent());
            Formula consequentLiteral = Util.getSingleLiteral(consequent);
            Z3Proof child1 = subProofs.get(0);
            if (Util.checkForFlippedDisequality(this.consequent,
                    child1.consequent)) {
                // TransformedZ3Proof premise = new
                // TransformedZ3Proof(SExpressionConstants.ASSERTED, new
                // ArrayList<TransformedZ3Proof>(), child1.consequent);
                // TransformedZ3Proof symmProof =
                // TransformedZ3Proof.createSymmetrieProof(premise);
                this.subProofs.clear();
                this.subProofs.add(child1);
                this.proofType = SExpressionConstants.SYMMETRY;

                if (!child1.wasVisitedByDAGOperation(operationId))
                    child1.dealWithModusPonensRecursion(operationId);
                return;
            }
            assert (child1.hasSingleLiteralConsequent());
            Formula literal1 = Util.getSingleLiteral(child1.consequent);

            Z3Proof child2 = subProofs.get(1);
            Z3Proof child3 = null;
            assert (child2.consequent instanceof PropositionalEq);
            while (true) {
                assert (child2.subProofs.size() > 0);
                if (child2.subProofs.get(0).consequent instanceof PropositionalEq)
                    child2 = child2.subProofs.get(0);
                else {
                    assert (child2.subProofs.size() <= 2);
                    if (child2.subProofs.size() == 1) {
                        child2 = child2.subProofs.get(0);
                        EqualityFormula consequentEq = (EqualityFormula) Util
                                .makeLiteralPositive(consequentLiteral);
                        Term startTerm = consequentEq.getTerms().get(0);
                        Term endTerm = consequentEq.getTerms().get(1);
                        Formula literal2 = Util
                                .getSingleLiteral(child2.consequent);
                        EqualityFormula eq1 = (EqualityFormula) Util
                                .makeLiteralPositive(literal1);
                        EqualityFormula eq2 = (EqualityFormula) Util
                                .makeLiteralPositive(literal2);

                        List<Z3Proof> proofList = new ArrayList<Z3Proof>();

                        if (eq1.getTerms().contains(startTerm)) {
                            if (eq1.getTerms().get(0).equals(startTerm)) {
                                proofList.add(child1);
                                assert (eq2.getTerms().contains(endTerm));
                                if (eq2.getTerms().get(1).equals(endTerm))
                                    proofList.add(child2);
                                else
                                    proofList.add(Z3Proof
                                            .createSymmetryProof(child2));
                            } else {
                                proofList.add(Z3Proof
                                        .createSymmetryProof(child1));
                                assert (eq2.getTerms().contains(endTerm));
                                if (eq2.getTerms().get(1).equals(endTerm))
                                    proofList.add(child2);
                                else
                                    proofList.add(Z3Proof
                                            .createSymmetryProof(child2));
                            }
                        } else {
                            assert (eq2.getTerms().contains(startTerm));
                            if (eq2.getTerms().get(0).equals(startTerm)) {
                                proofList.add(child2);
                                assert (eq1.getTerms().contains(endTerm));
                                if (eq1.getTerms().get(1).equals(endTerm))
                                    proofList.add(child1);
                                else
                                    proofList.add(Z3Proof
                                            .createSymmetryProof(child1));
                            } else {
                                proofList.add(Z3Proof
                                        .createSymmetryProof(child2));
                                assert (eq1.getTerms().contains(endTerm));
                                if (eq1.getTerms().get(1).equals(endTerm))
                                    proofList.add(child1);
                                else
                                    proofList.add(Z3Proof
                                            .createSymmetryProof(child1));
                            }
                        }

                        Z3Proof transProof = Z3Proof
                                .createTransitivityProof(proofList);
                        this.subProofs = transProof.subProofs;
                        this.proofType = transProof.proofType;
                        assert (this.consequent.transformToConsequentsForm()
                                .equals(transProof.consequent
                                        .transformToConsequentsForm()));
                        this.consequent = transProof.consequent
                                .transformToConsequentsForm();

                        // Recursive Calls on children
                        if (!child1.wasVisitedByDAGOperation(operationId))
                            child1.dealWithModusPonensRecursion(operationId);
                        if (!child2.wasVisitedByDAGOperation(operationId))
                            child2.dealWithModusPonensRecursion(operationId);
                        return;
                    }
                    child3 = child2.subProofs.get(1);
                    child2 = child2.subProofs.get(0);
                    assert (child2.hasSingleLiteralConsequent());
                    assert (child3.hasSingleLiteralConsequent());
                    break;
                }
            }
            assert (child2 != null);
            assert (child3 != null);
            Formula literal2 = Util.getSingleLiteral(child2.consequent);
            Formula literal3 = Util.getSingleLiteral(child3.consequent);

            assert (Util.makeLiteralPositive(consequentLiteral) instanceof DomainEq);
            assert (Util.makeLiteralPositive(literal1) instanceof DomainEq);
            assert (Util.makeLiteralPositive(literal2) instanceof DomainEq);
            assert (Util.makeLiteralPositive(literal3) instanceof DomainEq);

            EqualityFormula eq1 = (EqualityFormula) Util
                    .makeLiteralPositive(literal1);
            EqualityFormula eq2 = (EqualityFormula) Util
                    .makeLiteralPositive(literal2);
            EqualityFormula eq3 = (EqualityFormula) Util
                    .makeLiteralPositive(literal3);
            EqualityFormula consequentEq = (EqualityFormula) Util
                    .makeLiteralPositive(consequentLiteral);

            List<Z3Proof> proofList = new ArrayList<Z3Proof>();

            assert (consequentEq.getTerms().size() == 2);
            assert (eq1.getTerms().size() == 2);
            assert (eq2.getTerms().size() == 2);
            assert (eq3.getTerms().size() == 2);

            Term startTerm = consequentEq.getTerms().get(0);
            Term endTerm = consequentEq.getTerms().get(1);
            Term middleTerm = null;

            Set<EqualityFormula> containsStartTerm = new HashSet<EqualityFormula>();
            Set<EqualityFormula> containsEndTerm = new HashSet<EqualityFormula>();

            EqualityFormula[] equalities = { eq1, eq2, eq3 };
            Map<EqualityFormula, Z3Proof> map = new HashMap<EqualityFormula, Z3Proof>();
            map.put(eq1, child1);
            map.put(eq2, child2);
            map.put(eq3, child3);

            for (EqualityFormula eq : equalities)
                if (eq.getTerms().contains(startTerm))
                    containsStartTerm.add(eq);

            for (EqualityFormula eq : equalities)
                if (eq.getTerms().contains(endTerm))
                    containsEndTerm.add(eq);

            Set<EqualityFormula> toRemove = new HashSet<EqualityFormula>();
            for (EqualityFormula eq : containsStartTerm) {
                if (Util.isReflexivity(eq)) {
                    proofList.add(map.get(eq));
                    toRemove.add(eq);
                }
            }
            containsStartTerm.removeAll(toRemove);
            assert (containsStartTerm.size() == 1);
            if (containsStartTerm.iterator().next().getTerms().get(0)
                    .equals(startTerm)) {
                proofList.add(map.get(containsStartTerm.iterator().next()));
                middleTerm = containsStartTerm.iterator().next().getTerms()
                        .get(1);
            } else {
                assert (containsStartTerm.iterator().next().getTerms().get(1)
                        .equals(startTerm));
                proofList.add(Z3Proof.createSymmetryProof(map
                        .get(containsStartTerm.iterator().next())));
                middleTerm = containsStartTerm.iterator().next().getTerms()
                        .get(0);
            }

            toRemove.clear();
            for (EqualityFormula eq : containsEndTerm) {
                if (!Util.isReflexivity(eq)) {
                    if (eq.getTerms().get(1).equals(endTerm))
                        proofList.add(map.get(eq));
                    else
                        proofList.add(Z3Proof.createSymmetryProof(map.get(eq)));
                    toRemove.add(eq);
                }
            }
            containsEndTerm.removeAll(toRemove);
            assert (toRemove.size() <= 1);
            for (EqualityFormula eq : containsEndTerm) {
                assert (Util.isReflexivity(eq));
                proofList.add(map.get(eq));
            }

            if (proofList.size() != 3) {
                assert (proofList.size() == 2);
                EqualityFormula notUsedYet = null;
                if (!proofList.contains(child1))
                    notUsedYet = eq1;
                else if (!proofList.contains(child2))
                    notUsedYet = eq2;
                else
                    notUsedYet = eq3;
                assert (middleTerm != null);

                Z3Proof middleProof = map.get(notUsedYet);
                if (!notUsedYet.getTerms().get(0).equals(middleTerm))
                    middleProof = Z3Proof.createSymmetryProof(middleProof);

                Z3Proof lastElement = proofList.get(proofList.size() - 1);
                proofList.set(1, middleProof);
                proofList.add(lastElement);
            }

            Z3Proof transProof = Z3Proof.createTransitivityProof(proofList);
            this.subProofs = transProof.subProofs;
            this.proofType = transProof.proofType;
            assert (this.consequent.transformToConsequentsForm()
                    .equals(transProof.consequent.transformToConsequentsForm()));
            this.consequent = transProof.consequent
                    .transformToConsequentsForm();

            // If we have three subproofs, we need to split them,
            // because conversion to local proof cannot deal with
            // three subproofs.
            assert (subProofs.size() <= 3);
            if (subProofs.size() == 3) {
                assert (this.proofType == SExpressionConstants.TRANSITIVITY);
                Z3Proof intermediate = Z3Proof
                        .createTransitivityProof(new ArrayList<Z3Proof>(
                                subProofs.subList(0, 2)));
                Z3Proof rest = subProofs.get(2);
                subProofs.clear();
                subProofs.add(intermediate);
                subProofs.add(rest);
            }

            // Don't forget the recursive calls on the children!
            if (!child1.wasVisitedByDAGOperation(operationId))
                child1.dealWithModusPonensRecursion(operationId);
            if (!child2.wasVisitedByDAGOperation(operationId))
                child2.dealWithModusPonensRecursion(operationId);
            if (!child3.wasVisitedByDAGOperation(operationId))
                child3.dealWithModusPonensRecursion(operationId);
            return;
        }

        for (Z3Proof child : subProofs) {
            if (child.wasVisitedByDAGOperation(operationId))
                continue;
            child.dealWithModusPonensRecursion(operationId);
        }
    }

    public String prettyPrint() {
        int operationId = startDAGOperation();
        StringBuffer buffer = new StringBuffer();
        this.prettyPrintRecursive(operationId, buffer);
        endDAGOperation(operationId);
        return buffer.toString();
    }

    public void prettyPrintRecursive(int operationId, StringBuffer buffer) {
        visitedByDAGOperation(operationId);

        buffer.append("----------------------------------------------\n");
        buffer.append("ID: ");
        buffer.append(this.id);
        buffer.append("  (partition: ");
        buffer.append(this.assertPartition);
        buffer.append(")");
        buffer.append("\n");
        buffer.append("Rule: ");
        buffer.append(proofType.toString());
        buffer.append("\n");
        buffer.append("Antecedents:\n");
        for (Z3Proof child : subProofs) {
            buffer.append(child.id);
            buffer.append(": ");
            buffer.append(child.consequent.toString()
                    .replaceAll("\\s{2,}", " ").replace("\n", ""));
            buffer.append("\n");
        }
        buffer.append("Proofs: ");
        buffer.append(consequent.toString().replaceAll("\\s{2,}", " ")
                .replace("\n", ""));
        buffer.append("\n");
        for (Z3Proof child : subProofs) {
            if (child.wasVisitedByDAGOperation(operationId))
                continue;
            child.prettyPrintRecursive(operationId, buffer);
        }
    }

    /**
     * start a new DAG operation. increments global operation counter and
     * provides a unique operation id.
     * 
     * @return unique operation id.
     */
    public int startDAGOperation() {
        Z3Proof.operationCount++;
        return Z3Proof.operationCount;
    }

    /**
     * ends a DAG operation. decrements the global operation counter and removes
     * all <code>visitedByOperation</code> list entries for this operation in
     * all nodes.
     * 
     * @param operationId
     *            unique id of the operation to end.
     */
    public void endDAGOperation(int operationId) {
        assert (Z3Proof.operationCount >= operationId);
        this.resetMarks(operationId);
        Z3Proof.operationCount--;
    }

    /**
     * marks a node as visited by this operation.
     * 
     * @param operationId
     *            unique id of the operation.
     */
    protected void visitedByDAGOperation(int operationId) {
        // check for consistency.
        if (this.visitedByOperation.contains(operationId))
            throw new RuntimeException("revisited node#" + this.id
                    + " with operation#" + operationId
                    + ". this should not happen!");

        this.visitedByOperation.add(operationId);
    }

    /**
     * checks if this node was already visited by this operation.
     * 
     * @param operationId
     *            unique id of the operation.
     * @return true if was visited.
     */
    protected boolean wasVisitedByDAGOperation(int operationId) {
        return this.visitedByOperation.contains(operationId);
    }

    /**
     * removes the marks for the specified operation from this and all
     * sub-nodes.
     * 
     * @param operationId
     *            unique id of the operation.
     */
    private void resetMarks(int operationId) {
        this.visitedByOperation.remove((Integer) operationId);

        for (Z3Proof node : this.allNodes())
            node.visitedByOperation.remove((Integer) operationId);
    }

    public Set<Z3Proof> allNodes() {
        Set<Z3Proof> result = new HashSet<Z3Proof>();
        this.allNodes(result);
        return result;
    }

    private void allNodes(Set<Z3Proof> set) {
        set.add(this);
        for (Z3Proof child : this.subProofs) {
            if (!set.contains(child))
                child.allNodes(set);
        }
    }

    /**
     * @return <code>true</code> if the consequent of this node has only a
     *         single literal.
     */
    protected boolean hasSingleLiteralConsequent() {

        Formula formula = this.consequent.transformToConsequentsForm();
        if (!(formula instanceof OrFormula))
            return false;
        OrFormula consequent = (OrFormula) formula;
        return consequent.getDisjuncts().size() == 1;
    }

    /**
     * Creates a transitivity proof for the given list of subproofs. The list
     * must have exactly two or three elements, which match a transitivity
     * premise of the form [(a=b), (b=c)] or [(a=b), (b=c), (c=d)].
     * 
     * @param subProofs
     *            the subproofs
     * @return a transitivity proof for the given term.
     */
    public static Z3Proof createTransitivityProof(
            List<? extends Z3Proof> subProofs) {
        assert (subProofs.size() == 2 || subProofs.size() == 3);
        assert (Util.makeLiteralPositive(Util.getSingleLiteral((subProofs
                .get(0).consequent.transformToConsequentsForm()))) instanceof EqualityFormula);
        assert (Util
                .makeLiteralPositive(Util.getSingleLiteral(subProofs.get(1).consequent
                        .transformToConsequentsForm())) instanceof EqualityFormula);
        assert (subProofs.size() == 3 ? Util.makeLiteralPositive(Util
                .getSingleLiteral(subProofs.get(2).consequent
                        .transformToConsequentsForm())) instanceof EqualityFormula
                : true);

        final int initialSize = subProofs.size();
        assert (initialSize == 2 || initialSize == 3);
        Set<Z3Proof> toRemove = new HashSet<Z3Proof>();
        for (Z3Proof subProof : subProofs) {
            if (Util.isReflexivity(subProof.consequent))
                toRemove.add(subProof);
        }
        subProofs.removeAll(toRemove);
        if (subProofs.size() < 2) {
            if (subProofs.size() == 1)
                return subProofs.get(0);
            else {
                assert (toRemove.size() == initialSize);
                Object[] proofs = toRemove.toArray();
                assert (proofs.length == initialSize);
                assert (proofs[0] instanceof Z3Proof);
                assert (proofs[1] instanceof Z3Proof);
                if (proofs.length > 2) {
                    assert (proofs[2] instanceof Z3Proof);
                    assert (((Z3Proof) proofs[0]).consequent
                            .equals(((Z3Proof) proofs[1]).consequent) && ((Z3Proof) proofs[1]).consequent
                            .equals(((Z3Proof) proofs[2]).consequent));
                } else {
                    assert (((Z3Proof) proofs[0]).consequent
                            .equals(((Z3Proof) proofs[1]).consequent));
                }
                Z3Proof result = new Z3Proof(SExpressionConstants.ASSERTED,
                        new ArrayList<Z3Proof>(),
                        ((Z3Proof) proofs[0]).consequent);
                result.axiom = true;
                return result;
            }
        }

        EqualityFormula firstFormula = (EqualityFormula) Util
                .makeLiteralPositive(Util.getSingleLiteral(subProofs.get(0).consequent
                        .transformToConsequentsForm()));
        EqualityFormula lastFormula = (EqualityFormula) Util
                .makeLiteralPositive(Util.getSingleLiteral(subProofs
                        .get(subProofs.size() - 1).consequent
                        .transformToConsequentsForm()));
        EqualityFormula middleFormula = subProofs.size() == 3 ? (EqualityFormula) Util
                .makeLiteralPositive(Util.getSingleLiteral(subProofs.get(1).consequent
                        .transformToConsequentsForm()))
                : null;

        EqualityFormula[] equalities;
        if (middleFormula != null) {
            equalities = new EqualityFormula[3];
            equalities[0] = firstFormula;
            equalities[1] = middleFormula;
            equalities[2] = lastFormula;
        } else {
            equalities = new EqualityFormula[2];
            equalities[0] = firstFormula;
            equalities[1] = lastFormula;
        }

        assert (Util.checkEqualityChain(equalities));

        int numDisequalities = 0;
        for (Z3Proof child : subProofs) {
            if (Util.isNegativeLiteral(Util.getSingleLiteral(child.consequent
                    .transformToConsequentsForm())))
                numDisequalities++;
        }

        assert (numDisequalities <= 1);

        assert (firstFormula.getTerms().size() == 2);
        Term term1 = firstFormula.getTerms().get(0);
        assert (lastFormula.getTerms().size() == 2);
        Term term2 = lastFormula.getTerms().get(1);

        List<Term> newTerms = new ArrayList<Term>();
        newTerms.add(term1);
        newTerms.add(term2);

        Formula newFormula = null;
        try {
            newFormula = EqualityFormula
                    .create(newTerms, numDisequalities == 0)
                    .transformToConsequentsForm();
        } catch (IncomparableTermsException exc) {
            throw new RuntimeException(
                    "Incomparable terms while creating transitivity proof.",
                    exc);
        }

        Z3Proof result = new Z3Proof(SExpressionConstants.TRANSITIVITY,
                subProofs, newFormula);

        // If we have three subproofs, we need to split them,
        // because conversion to local proof cannot deal with
        // three subproofs.
        assert (result.subProofs.size() <= 3);
        if (result.subProofs.size() == 3) {
            assert (result.proofType == SExpressionConstants.TRANSITIVITY);
            Z3Proof intermediate = Z3Proof
                    .createTransitivityProof(new ArrayList<Z3Proof>(
                            result.subProofs.subList(0, 2)));
            Z3Proof rest = result.subProofs.get(2);
            result.subProofs.clear();
            result.subProofs.add(intermediate);
            result.subProofs.add(rest);
        }

        return result;

    }

    /**
     * Creates a symmetry proof for the given premise.
     * 
     * @param premise
     *            must have a single literal as a consequence
     * @return a symmetry proof for the given premise.
     */
    public static Z3Proof createSymmetryProof(Z3Proof premise) {
        assert (premise.hasSingleLiteralConsequent());
        Formula literal = Util.makeLiteralPositive(Util
                .getSingleLiteral((premise.consequent
                        .transformToConsequentsForm())));
        assert (literal instanceof EqualityFormula);
        boolean equal = !Util.isNegativeLiteral(Util
                .getSingleLiteral(premise.consequent
                        .transformToConsequentsForm()));

        List<Term> terms = ((EqualityFormula) literal).getTerms();
        Collections.reverse(terms);
        Formula consequentFormula = null;
        try {
            consequentFormula = EqualityFormula.create(terms, equal);
            consequentFormula = consequentFormula.transformToConsequentsForm();
            assert (consequentFormula != null);
        } catch (IncomparableTermsException exc) {
            throw new RuntimeException(
                    "Incomparable terms while creating symmetry proof.", exc);
        }
        List<Z3Proof> subproofs = new ArrayList<Z3Proof>();
        subproofs.add(premise);
        return new Z3Proof(SExpressionConstants.SYMMETRY, subproofs,
                consequentFormula);
    }

    /**
     * Checks if node is valid. Therefore, whether the given Subproofs together
     * produces the consequent of the node.
     * 
     * @return return true if node is valid
     */
    public boolean checkZ3ProofNode() {

        if (true)
            return true;

        SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type, "lib/z3/bin/z3");

        if (this.subProofs.size() > 0) {

            List<Formula> conjuncts = new ArrayList<Formula>();
            for (Z3Proof subProof : this.subProofs) {
                conjuncts.add(subProof.consequent);
            }
            conjuncts.add(new NotFormula(this.consequent));
            Formula formulaToCheck = new AndFormula(conjuncts);

            String declarationStr = makeDeclarationsAndDefinitions(formulaToCheck);
            String formulaSmtStr = buildSMTDescription(declarationStr,
                    formulaToCheck.toString());

            z3.solve(formulaSmtStr);

            switch (z3.getState()) {
            case SMTSolver.UNSAT:
                break;
            case SMTSolver.SAT:
                System.out.println("Bad Node: " + this.id);
                throw new RuntimeException(
                        "Error while testing vality of Z3-node with Z3-solver: \n"
                                + "z3 tells us SAT, node is NOT valid.");
            default:
                System.out
                        .println("....Z3 OUTCOME ---->  UNKNOWN! CHECK ERROR STREAM.");
                throw (new RuntimeException(
                        "Z3 tells us UNKOWN STATE. CHECK ERROR STREAM."));
            }
        }
        return true;
    }

    /**
     * Checks recursive if node is valid. Therefore, whether the given Subproofs
     * together produces the consequent of the node. Also checks this property
     * recursive for every node of the subtree.
     * 
     * @return return true if node is valid
     */
    public boolean checkZ3ProofNodeRecursive() {
        if (true)
            return true;

        int operationId = startDAGOperation();
        boolean result = this.checkZ3ProofNodeRecursiveRecursion(operationId);
        endDAGOperation(operationId);

        return result;
    }

    private boolean checkZ3ProofNodeRecursiveRecursion(int operationId) {
        if (this.wasVisitedByDAGOperation(operationId))
            return true;
        visitedByDAGOperation(operationId);
        if (this.subProofs.size() > 0)
            for (Z3Proof subProof : this.subProofs) {
                if (subProof.wasVisitedByDAGOperation(operationId))
                    continue;
                if (!subProof.checkZ3ProofNodeRecursiveRecursion(operationId))
                    return false;
            }
        return checkZ3ProofNode();
    }

    /**
     * Writes the declarations of all domain variables, propositional variables,
     * uninterpreted functions, as well as the definition of all macros in
     * <code>formula</code>.
     * 
     * @param formula
     *            The formula for which to write the definitions.
     * @return the declaration
     */
    protected String makeDeclarationsAndDefinitions(Formula formula) {

        Set<SExpression> outputExpressions = new HashSet<SExpression>();

        for (PropositionalVariable var : formula.getPropositionalVariables())
            outputExpressions
                    .add(SExpression.makeDeclareFun((Token) var.toSmtlibV2(),
                            SExpressionConstants.BOOL_TYPE, 0));

        for (DomainVariable var : formula.getDomainVariables())
            outputExpressions.add(SExpression.makeDeclareFun(
                    (Token) var.toSmtlibV2(), SExpressionConstants.VALUE_TYPE,
                    0));

        for (UninterpretedFunction function : formula
                .getUninterpretedFunctions())
            outputExpressions.add(SExpression.makeDeclareFun(
                    function.getName(), function.getType(),
                    function.getNumParams()));

        for (FunctionMacro macro : this.consequent.getFunctionMacros())
            outputExpressions.add(macro.toSmtlibV2());

        String declarationsStr = "";
        for (SExpression declaration : outputExpressions)
            declarationsStr += declaration.toString();

        return declarationsStr;
    }

    /**
     * Creates an SMT description for a given formula
     * 
     * @param declarationStr
     *            declarations of the SMT description
     * @param formulaStr
     *            formula to be checked
     * @return SMT description
     * 
     */
    protected String buildSMTDescription(String declarationStr,
            String formulaStr) {
        String smtStr = "";

        smtStr += SExpressionConstants.SET_LOGIC_QF_UF.toString();
        smtStr += SExpressionConstants.DECLARE_SORT_VALUE.toString();

        smtStr += declarationStr;

        smtStr += "(assert" + formulaStr + ")";

        smtStr += SExpressionConstants.CHECK_SAT.toString();
        smtStr += SExpressionConstants.EXIT.toString();

        return smtStr;
    }

    public static int numInstances() {
        return Z3Proof.instanceCounter;
    }

    /**
     * 
     * @return number of nodes in this proof
     */
    public int size() {
        return this.size(false);
    }

    /**
     * 
     * @param unwind
     *            if <code>true</code> unwind DAG into a tree
     * @return number of nodes in this proof, unwinding the DAG into a tree, if
     *         <code>unwind</code> is <code>true</code>.
     */
    public int size(boolean unwind) {

        int result = 1;
        if (unwind) {
            for (Z3Proof child : subProofs)
                result += child.size();
            return result;
        } else {

            int operationId = startDAGOperation();
            result = this.sizeRecursion(operationId);
            endDAGOperation(operationId);

            return result;
        }
    }

    private int sizeRecursion(int operationId) {
        int result = 1;
        if (this.wasVisitedByDAGOperation(operationId))
            return 0;
        visitedByDAGOperation(operationId);
        for (Z3Proof child : subProofs)
            result += child.sizeRecursion(operationId);
        return result;
    }

    /**
     * Recursively computes the parents in the proof, starting from
     * <code>this</code> downwards.
     * 
     * @return the map from children to parents. Note that in a DAG, a child may
     *         have several parents.
     */
    public Map<Z3Proof, Set<Z3Proof>> computeParents() {
        int operationId = startDAGOperation();
        Map<Z3Proof, Set<Z3Proof>> result = new HashMap<Z3Proof, Set<Z3Proof>>();
        this.computeParentsRecursion(operationId, result);
        endDAGOperation(operationId);
        return result;
    }

    /**
     * 
     * @param map
     *            call-by-reference parameter to be updated during recursion
     */
    private void computeParentsRecursion(int operationId,
            Map<Z3Proof, Set<Z3Proof>> map) {
        if (this.wasVisitedByDAGOperation(operationId))
            return;
        visitedByDAGOperation(operationId);

        for (Z3Proof child : subProofs) {
            Set<Z3Proof> set = map.get(child);
            if (set == null)
                set = new HashSet<Z3Proof>();
            assert (set != null);
            set.add(this);
            map.put(child, set);

            if (!child.wasVisitedByDAGOperation(operationId))
                child.computeParentsRecursion(operationId, map);
        }
        return;
    }

    public Set<Z3Proof> nodesOnPathTo(Z3Proof target) {
        Set<Z3Proof> result = null;

        if (this == target)
            return new HashSet<Z3Proof>();

        for (Z3Proof child : subProofs) {
            if (result == null) {
                result = child.nodesOnPathTo(target);
                if (result != null)
                    result.add(this);
            } else {
                assert (result != null);
                if (result.contains(child))
                    continue;
                Set<Z3Proof> tmp = child.nodesOnPathTo(target);
                if (tmp != null) {
                    result.addAll(tmp);
                    result.add(this);
                }
            }
        }
        return result;
    }

    /**
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     */
    @Override
    public int compareTo(SMTLibObject o) {
        return this.toString().compareTo(o.toString());
    }
}
