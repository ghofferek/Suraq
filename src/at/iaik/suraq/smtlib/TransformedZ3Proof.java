/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.IncomparableTermsException;
import at.iaik.suraq.exceptions.WrongFunctionTypeException;
import at.iaik.suraq.exceptions.WrongNumberOfParametersException;
import at.iaik.suraq.proof.AnnotatedProofNode;
import at.iaik.suraq.proof.AnnotatedProofNodes;
import at.iaik.suraq.resProof.Lit;
import at.iaik.suraq.resProof.ResNode;
import at.iaik.suraq.resProof.ResProof;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.smtlib.formula.PropositionalIte;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.util.Util;

/**
 * 
 * Should only contain the following proof rules: Asserted, Symmetry, (simple,
 * i.e., 2-subproof) Transitivity, Monotonicity and (simple, i.e. 2-subproof)
 * Resolution.
 * 
 * Formulas for consequents should have the following structure: - each atom is
 * either a positive equality of two terms, a propositional variable, or an
 * uninterpreted predicate - each literal is either an atom or a negation of an
 * atom - formula is always an or formula which consists of at least one literal
 * 
 * Formulas for literals should be positive atoms as defined above.
 * 
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
public class TransformedZ3Proof extends Z3Proof {

    public static TransformedZ3Proof debugNode = null;

    /**
     * This maps IDs of Z3Proofs to their TransformedZ3Proof counterparts. This
     * is to avoid DAG unwinding during conversion.
     */
    private static Map<Integer, TransformedZ3Proof> proofMap = new HashMap<Integer, TransformedZ3Proof>();

    /**
     * The "literal" on which resolution is applied. This could e.g. be an
     * equality of the form (a=b), or (f(a)=c). It could also be a propositional
     * variable, or an (uninterpreted) predicate instance. <code>literal</code>
     * will be <code>null</code> for leaves of the proof. In non-leave nodes,
     * <code>literal</code> should store the positive (=non-negated) form of the
     * resolution literal. I.e., <code>literal</code> should not be of type
     * <code>NotFormula</code>.
     */
    private Formula literal = null;

    /**
     * Indicates that this proof object is a hypothesis. This implies that it is
     * also a leave.
     */
    private boolean hypothesis = false;

    /**
     * >>>>>>> .r376 Storage for annotated nodes used during proof conversion.
     */
    private static AnnotatedProofNodes annotatedNodes = new AnnotatedProofNodes();

    /**
     * Creates a new <code>TransformedZ3Proof</code>.
     * 
     * @param proofType
     *            type of the proof.
     * @param subProofs
     *            the subproofs.
     * @param consequent
     *            the consequent.
     * 
     */
    public TransformedZ3Proof(Token proofType,
            List<TransformedZ3Proof> subProofs, Formula consequent) {

        super(proofType, subProofs, consequent.transformToConsequentsForm()
                .deepFormulaCopy());
        if (this.id == 548)
            this.checkZ3ProofNodeRecursive();
        assert (this.checkZ3ProofNode());
    }

    /**
     * Creates a new <code>TransformedZ3Proof</code>.
     * 
     * @param proofType
     *            type of the proof.
     * @param subProofs
     *            the subproofs.
     * @param literal
     *            the literal of the resolution proof.
     * @param consequent
     *            the consequent.
     * 
     */
    public TransformedZ3Proof(Token proofType,
            List<TransformedZ3Proof> subProofs, Formula literal,
            Formula consequent) {

        super(proofType, subProofs, consequent.transformToConsequentsForm()
                .deepFormulaCopy());

        this.literal = literal == null ? null : Util.getSingleLiteral(literal
                .deepFormulaCopy());
        if (this.id == 548)
            this.checkZ3ProofNodeRecursive();
        assert (this.checkZ3ProofNode());
    }

    /**
     * Creates a new <code>TransformedZ3Proof</code>.
     * 
     * @param proofType
     *            type of the proof.
     * @param subProof1
     *            the first subproof.
     * @param subProof2
     *            the second subproof.
     * @param literal
     *            the literal of the resolution proof.
     * @param consequent
     *            the consequent.
     * 
     */
    public TransformedZ3Proof(Token proofType, Z3Proof subProof1,
            Z3Proof subProof2, Formula literal, Formula consequent) {

        super(proofType, subProof1, subProof2, consequent
                .transformToConsequentsForm().deepFormulaCopy());

        this.literal = literal == null ? null : Util.getSingleLiteral(literal
                .deepFormulaCopy());
        if (this.id == 548 || subProof1.id == 548 || subProof2.id == 548)
            this.checkZ3ProofNodeRecursive();
        assert (this.checkZ3ProofNode());
    }

    public TransformedZ3Proof(ResNode node, Map<Integer, Formula> literalMap) {

        // FIXME Don't unwind the DAG! Reuse nodes where possible!

        if (!node.isLeaf) { // CREATE RESOLUTION NODE

            this.proofType = SExpressionConstants.UNIT_RESOLUTION;
            this.literal = literalMap.get(node.pivot);

            this.subProofs.add(new TransformedZ3Proof(node.left, literalMap));
            this.subProofs.add(new TransformedZ3Proof(node.right, literalMap));
        } else { // CREATE ASSERTED NODE

            this.proofType = SExpressionConstants.ASSERTED;
        }

        // build consequent from clause
        List<Formula> disjuncts = new ArrayList<Formula>();
        for (Lit literal : node.cl) {
            Formula elem = literalMap.get(literal.var());
            if (!literal.isPos())
                elem = new NotFormula(elem);
            disjuncts.add(elem);
        }

        if (disjuncts.size() == 0)
            disjuncts.add(new PropositionalConstant(false));

        this.consequent = new OrFormula(disjuncts);

        // TODO Check: Should this be set for leafs only?
        this.assertPartition = node.part;
    }

    public static TransformedZ3Proof convertToTransformedZ3Proof(Z3Proof z3Proof) {

        TransformedZ3Proof.debugNode = TransformedZ3Proof.proofMap.get(307);

        if (TransformedZ3Proof.proofMap.containsKey(z3Proof.id))
            // return TransformedZ3Proof.proofMap.get(z3Proof.id);
            TransformedZ3Proof.proofMap.remove(z3Proof.id);

        // Go through all possible cases of z3 proof rules

        Token proofType = z3Proof.getProofType();

        if (proofType.equals(SExpressionConstants.AND_ELIM)
                || proofType.equals(SExpressionConstants.NOT_OR_ELIM)
                || proofType.equals(SExpressionConstants.REWRITE)
                || proofType.equals(SExpressionConstants.ASSERTED)
                || proofType.equals(SExpressionConstants.COMMUTATIVITY)) {
            // Treat this as a leave.
            // Relies on the assumption that and-elim (not-or-elim) is only used
            // for things that have been asserted, and not on things are are
            // proven separately.

            if (!(z3Proof.subProofs.size() == 0))
                throw new RuntimeException(
                        "Asserted Node should not have children");

            TransformedZ3Proof result = new TransformedZ3Proof(
                    SExpressionConstants.ASSERTED,
                    new ArrayList<TransformedZ3Proof>(), z3Proof
                            .getConsequent().transformToConsequentsForm());
            assert (!TransformedZ3Proof.proofMap.containsKey(z3Proof.id));
            TransformedZ3Proof.proofMap.put(z3Proof.id, result);
            return result;

        } else if (proofType.equals(SExpressionConstants.HYPOTHESIS)) {
            // Treat this as a leave.
            if (!(z3Proof.subProofs.size() == 0))
                throw new RuntimeException(
                        "Asserted Node should not have children");

            TransformedZ3Proof result = new TransformedZ3Proof(
                    SExpressionConstants.ASSERTED,
                    new ArrayList<TransformedZ3Proof>(), z3Proof
                            .getConsequent().transformToConsequentsForm());
            result.hypothesis = true;
            assert (!TransformedZ3Proof.proofMap.containsKey(z3Proof.id));
            TransformedZ3Proof.proofMap.put(z3Proof.id, result);
            return result;

        } else if (proofType.equals(SExpressionConstants.AXIOM)
                || proofType.equals(SExpressionConstants.REFLEXIVITY)) {
            // Treat this as a leave.
            // It should be a propositional tautology.
            if (!(z3Proof.subProofs.size() == 0))
                throw new RuntimeException(
                        "Asserted Node should not have children");

            TransformedZ3Proof result = new TransformedZ3Proof(
                    SExpressionConstants.ASSERTED,
                    new ArrayList<TransformedZ3Proof>(), z3Proof
                            .getConsequent().transformToConsequentsForm());
            result.axiom = true;
            assert (!TransformedZ3Proof.proofMap.containsKey(z3Proof.id));
            TransformedZ3Proof.proofMap.put(z3Proof.id, result);
            return result;

        } else if (proofType.equals(SExpressionConstants.MODUS_PONENS)) {

            // Given a proof for p and a proof for (implies p q), produces a
            // proof for q. The second antecedents may also be a proof for (iff
            // p q).

            // should already have been removed
            assert (false);
            return null;

        } else if (proofType.equals(SExpressionConstants.UNIT_RESOLUTION)) {

            List<Z3Proof> z3SubProofs = z3Proof.getSubProofs();
            assert (z3SubProofs.size() >= 2);

            TransformedZ3Proof transformedAntecedent = TransformedZ3Proof
                    .convertToTransformedZ3Proof(z3SubProofs.get(0));

            assert (transformedAntecedent.consequent instanceof OrFormula);

            OrFormula remainingFormula = (OrFormula) transformedAntecedent.consequent;

            for (int count = 1; count < z3SubProofs.size() - 1; count++) {
                List<Formula> newDisjuncts = remainingFormula.getDisjuncts();

                Formula resolutionAssociate = Util.getSingleLiteral(z3SubProofs
                        .get(count).getConsequent()
                        .transformToConsequentsForm());

                if (!(Util.isLiteral(resolutionAssociate)))
                    throw new RuntimeException(
                            "Resolution associate should be a literal");

                Formula invLiteral = Util.invertLiteral(resolutionAssociate);
                Formula posLiteral = Util
                        .makeLiteralPositive(resolutionAssociate);

                if (!newDisjuncts.remove(invLiteral))
                    throw new RuntimeException(
                            "Problem in Unit Resolution Transformation:\n"
                                    + "Literal was not present in the remaining formula:\n "
                                    + "List of Literals:  " + remainingFormula
                                    + "given Literal:  " + invLiteral);

                remainingFormula = new OrFormula(newDisjuncts);

                transformedAntecedent = new TransformedZ3Proof(
                        SExpressionConstants.UNIT_RESOLUTION,
                        TransformedZ3Proof
                                .convertToTransformedZ3Proof(z3SubProofs
                                        .get(count)), transformedAntecedent,
                        posLiteral,
                        remainingFormula.transformToConsequentsForm());

            }

            List<TransformedZ3Proof> subproofs = new ArrayList<TransformedZ3Proof>();
            subproofs.add(transformedAntecedent);
            subproofs.add(TransformedZ3Proof
                    .convertToTransformedZ3Proof(z3SubProofs.get(z3SubProofs
                            .size() - 1)));
            TransformedZ3Proof result = new TransformedZ3Proof(
                    proofType = SExpressionConstants.UNIT_RESOLUTION,
                    subproofs, z3Proof.getConsequent()
                            .transformToConsequentsForm());

            Formula resolutionAssociate = z3SubProofs
                    .get(z3SubProofs.size() - 1).getConsequent()
                    .transformToConsequentsForm();

            assert (resolutionAssociate instanceof OrFormula);
            result.literal = Util.findResolvingLiteral(
                    (OrFormula) resolutionAssociate, transformedAntecedent
                            .getConsequent().transformToConsequentsForm());

            result.consequent = z3Proof.getConsequent()
                    .transformToConsequentsForm();
            assert (!TransformedZ3Proof.proofMap.containsKey(z3Proof.id));
            TransformedZ3Proof.proofMap.put(z3Proof.id, result);
            return result;

        } else if (proofType.equals(SExpressionConstants.LEMMA)) {

            if (z3Proof.id == 548)
                assert (z3Proof.checkZ3ProofNodeRecursive());

            List<Z3Proof> z3SubProofs = z3Proof.getSubProofs();
            if (z3SubProofs.size() != 1)
                throw new RuntimeException(
                        "Lemma proof with not exactly one child. This should not happen!");

            Z3Proof hypotheticalProof = z3SubProofs.get(0);

            // assert (hypotheticalProof.checkZ3ProofNodeRecursive());
            hypotheticalProof.localLemmasToAssertions();

            // assert (hypotheticalProof.checkZ3ProofNodeRecursive());
            hypotheticalProof.removeLocalSubProofs();

            // assert (hypotheticalProof.checkZ3ProofNodeRecursive());
            hypotheticalProof.dealWithModusPonens();

            // assert (hypotheticalProof.checkZ3ProofNodeRecursive());
            TransformedZ3Proof transformedHypotheticalProof = TransformedZ3Proof
                    .convertToTransformedZ3Proof(hypotheticalProof);

            // assert
            // (transformedHypotheticalProof.checkZ3ProofNodeRecursive());
            transformedHypotheticalProof.toLocalProof();
            assert (transformedHypotheticalProof.isLocal());

            // assert
            // (transformedHypotheticalProof.checkZ3ProofNodeRecursive());
            transformedHypotheticalProof.toResolutionProof();

            // assert
            // (transformedHypotheticalProof.checkZ3ProofNodeRecursive());

            if (!transformedHypotheticalProof.consequent
                    .equals((new PropositionalConstant(false))
                            .transformToConsequentsForm()))
                throw new RuntimeException(
                        "Hypothetical proof (antecedent of lemma) does not prove false, but: "
                                + transformedHypotheticalProof.consequent
                                        .toString());

            assert (transformedHypotheticalProof.checkZ3ProofNodeRecursive());
            transformedHypotheticalProof.removeHypotheses();
            assert (transformedHypotheticalProof.checkZ3ProofNodeRecursive());

            List<TransformedZ3Proof> subProofs = new ArrayList<TransformedZ3Proof>();
            for (Z3Proof proof : transformedHypotheticalProof.subProofs) {
                assert (proof instanceof TransformedZ3Proof);
                subProofs.add((TransformedZ3Proof) proof);
            }

            TransformedZ3Proof result = new TransformedZ3Proof(
                    transformedHypotheticalProof.proofType, subProofs,
                    transformedHypotheticalProof.consequent);
            result.literal = Util
                    .getSingleLiteral(transformedHypotheticalProof.literal);

            // Remove stored conversion results for all subproofs
            // They are "tainted" by hypothesis removal.
            Set<Z3Proof> allSubNodes = z3Proof.allNodes();
            for (Z3Proof proof : allSubNodes)
                TransformedZ3Proof.proofMap.remove(proof);

            assert (!TransformedZ3Proof.proofMap.containsKey(z3Proof.id));
            TransformedZ3Proof.proofMap.put(z3Proof.id, result);
            assert (result.checkZ3ProofNode());
            return result;

        } else if (proofType.equals(SExpressionConstants.TRANSITIVITY)) {

            assert (z3Proof.subProofs.size() >= 2);
            TransformedZ3Proof current1 = TransformedZ3Proof
                    .convertToTransformedZ3Proof(z3Proof.subProofs.get(0));
            for (int count = 1; count < z3Proof.subProofs.size(); count++) {
                TransformedZ3Proof current2 = TransformedZ3Proof
                        .convertToTransformedZ3Proof(z3Proof.subProofs
                                .get(count));
                List<TransformedZ3Proof> currentSubProofs = new ArrayList<TransformedZ3Proof>(
                        2);
                currentSubProofs.add(current1);
                currentSubProofs.add(current2);
                current1 = TransformedZ3Proof
                        .createTransitivityProofForTransformedZ3Proofs(currentSubProofs);
                assert (current1.subProofs.size() == 2);
            }
            assert (!TransformedZ3Proof.proofMap.containsKey(z3Proof.id));
            TransformedZ3Proof.proofMap.put(z3Proof.id, current1);
            return current1;

        } else if (proofType.equals(SExpressionConstants.MONOTONICITY)
                || proofType.equals(SExpressionConstants.SYMMETRY)) {

            List<TransformedZ3Proof> subProofs = new ArrayList<TransformedZ3Proof>();
            for (Z3Proof proof : z3Proof.subProofs) {
                subProofs.add(TransformedZ3Proof
                        .convertToTransformedZ3Proof(proof));
            }
            TransformedZ3Proof result = new TransformedZ3Proof(proofType,
                    subProofs, z3Proof.getConsequent()
                            .transformToConsequentsForm());
            assert (!TransformedZ3Proof.proofMap.containsKey(z3Proof.id));
            TransformedZ3Proof.proofMap.put(z3Proof.id, result);
            return result;
        } else {
            throw new RuntimeException("Encountered unexpected proof rule "
                    + proofType.toString()
                    + " while trying to rewrite z3 proof.");
        }
    }

    public void toLocalProof() {
        TransformedZ3Proof.annotatedNodes.clear();

        int operationId = startDAGOperation();
        this.toLocalProofRecursion(operationId);
        endDAGOperation(operationId);

        TransformedZ3Proof.annotatedNodes.clear();
    }

    /**
     * Transforms the proof into a local resolution proof (in place).
     */
    private void toLocalProofRecursion(int operationId) {
        // this.computeParents(); // FIXME do we really need this?
        if (this.wasVisitedByDAGOperation(operationId))
            return;
        visitedByDAGOperation(operationId);
        for (Z3Proof child : subProofs) {
            assert (child instanceof TransformedZ3Proof);
            TransformedZ3Proof subProof = (TransformedZ3Proof) child;
            subProof.toLocalProofRecursion(operationId);
        }

        // Recursive calls are completed. Now handle this particular node.
        // -------------------------------------------------------------
        if (this.proofType.equals(SExpressionConstants.SYMMETRY)) {
            assert (this.hasSingleLiteralConsequent());
            assert (subProofs.size() == 1);
            Z3Proof subproof = subProofs.get(0);
            Formula premiseLiteral = ((OrFormula) (subproof.consequent))
                    .getDisjuncts().iterator().next();
            AnnotatedProofNode annotatedNode = TransformedZ3Proof.annotatedNodes
                    .getNodeWithConsequent(premiseLiteral);
            if (annotatedNode == null)
                throw new RuntimeException(
                        "No annotated proof node found when there should be one.");
            int numPremises = annotatedNode.numPremises();
            if (numPremises != 0 && numPremises != 3)
                throw new RuntimeException(
                        "Unexpected number of premises for annotated symmetry node: "
                                + (new Integer(numPremises)).toString());
            if (numPremises == 0) {
                assert (this.subProofs.size() == 1);
                Z3Proof premise = this.subProofs.get(0);
                assert (premise.hasSingleLiteralConsequent());
                TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(
                        annotatedNode.getPartition(), annotatedNode
                                .getPartition(), this, null, null, null));
            } else {
                assert (numPremises == 3);
                TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(
                        annotatedNode.getRightPartition(), annotatedNode
                                .getLeftPartition(), this, TransformedZ3Proof
                                .createSymmetryProof(annotatedNode
                                        .getPremise3()), TransformedZ3Proof
                                .createSymmetryProof(annotatedNode
                                        .getPremise2()), TransformedZ3Proof
                                .createSymmetryProof(annotatedNode
                                        .getPremise1())));
            }
            return;
        }

        // -------------------------------------------------------------
        if (this.proofType.equals(SExpressionConstants.TRANSITIVITY)) {
            assert (this.hasSingleLiteralConsequent());
            handleTransitivity();
            return;
        }

        // -------------------------------------------------------------
        if (this.proofType.equals(SExpressionConstants.MONOTONICITY)) {
            assert (this.hasSingleLiteralConsequent());
            handleMonotonicity();
            return;
        }

        // -------------------------------------------------------------
        if (this.hasSingleLiteralConsequent()) {
            Formula literal = ((OrFormula) (this.consequent)).getDisjuncts()
                    .iterator().next();
            Set<Integer> partitions = literal.getPartitionsFromSymbols();
            assert (partitions.size() > 0);
            partitions.remove(-1);
            if (partitions.size() > 1)
                // this is a bad literal. We ignore it. It will be
                // removed by this method anyway
                return;

            int partition;
            if (partitions.size() == 0)
                partition = 1; // put global stuff in partition 1 (arbitrary
                               // choice)
            else {
                assert (partitions.iterator().hasNext());
                assert (partitions.size() == 1);
                partition = partitions.iterator().next();
            }

            AnnotatedProofNode annotatedNode = new AnnotatedProofNode(
                    partition, partition, this, null, null, null);
            TransformedZ3Proof.annotatedNodes.add(annotatedNode);

            if (this.proofType.equals(SExpressionConstants.ASSERTED))
                // for UNIT-RESOLUTION we still need to update the subProofs
                return;
        }
        if (!this.hasSingleLiteralConsequent()
                || this.proofType.equals(SExpressionConstants.UNIT_RESOLUTION)) {

            // The following is based on the assumption that resolution uses
            // "bad" (=non-local) literals only if it directly concludes
            // "false".
            //
            // This is justified as follows:
            // The original formula does not use bad literals.
            // Theory rules produce only single-literal consequents.
            // Therefore, bad literals can only occur in unit clauses.
            // TODO Check if this assumption is valid. If not, change code
            // accordingly!

            assert (this.proofType.equals(SExpressionConstants.UNIT_RESOLUTION) || this.proofType
                    .equals(SExpressionConstants.ASSERTED));

            if (this.proofType.equals(SExpressionConstants.UNIT_RESOLUTION)) {
                // Update subproofs
                assert (subProofs.size() == 2); // Multi-resolution should
                                                // already have been removed

                assert (Util.checkResolutionNodeForBadLiterals(this));

                if (Util.isLiteral(subProofs.get(0).consequent)) {
                    AnnotatedProofNode annotatedNode = TransformedZ3Proof.annotatedNodes
                            .getNodeWithConsequent(Util
                                    .getSingleLiteral(subProofs.get(0).consequent));
                    if (annotatedNode != null) {
                        Z3Proof update = annotatedNode.getConsequent();
                        if (annotatedNode.numPremises() == 3) {
                            List<TransformedZ3Proof> transSubProofs = new ArrayList<TransformedZ3Proof>(
                                    3);
                            transSubProofs.add(annotatedNode.getPremise1());
                            transSubProofs.add(annotatedNode.getPremise2());
                            transSubProofs.add(annotatedNode.getPremise3());
                            update = TransformedZ3Proof
                                    .createTransitivityProofForTransformedZ3Proofs(transSubProofs);
                        }
                        assert (((TransformedZ3Proof) update).isLocal());
                        subProofs.set(0, update);
                    }
                }

                if (Util.isLiteral(subProofs.get(1).consequent)) {
                    AnnotatedProofNode annotatedNode2 = TransformedZ3Proof.annotatedNodes
                            .getNodeWithConsequent(Util
                                    .getSingleLiteral(subProofs.get(1).consequent));
                    if (annotatedNode2 != null) {
                        Z3Proof update = annotatedNode2.getConsequent();
                        if (annotatedNode2.numPremises() == 3) {
                            List<TransformedZ3Proof> transSubProofs = new ArrayList<TransformedZ3Proof>(
                                    3);
                            transSubProofs.add(annotatedNode2.getPremise1());
                            transSubProofs.add(annotatedNode2.getPremise2());
                            transSubProofs.add(annotatedNode2.getPremise3());
                            update = TransformedZ3Proof
                                    .createTransitivityProofForTransformedZ3Proofs(transSubProofs);
                        }
                        assert (((TransformedZ3Proof) update).isLocal());
                        subProofs.set(1, update);
                    }
                }
            }
            return;
        }

        // If we reach here, we are in case that was not foreseen.
        assert (false);
    }

    /**
     * 
     */
    private void handleMonotonicity() {
        assert (subProofs.size() >= 1);

        Formula literal = Util.getSingleLiteral(consequent);
        assert (literal instanceof DomainEq);
        DomainEq eqLiteral = (DomainEq) literal;
        assert (eqLiteral.getTerms().get(0) instanceof DomainTerm);
        DomainTerm leftTerm = (DomainTerm) eqLiteral.getTerms().get(0);
        assert (eqLiteral.getTerms().get(eqLiteral.getTerms().size() - 1) instanceof DomainTerm);
        DomainTerm rightTerm = (DomainTerm) eqLiteral.getTerms().get(
                eqLiteral.getTerms().size() - 1);

        Set<Integer> leftPartitions = leftTerm.getPartitionsFromSymbols();
        leftPartitions.remove(-1);
        assert (leftPartitions.size() <= 1);
        int leftPartition;
        Iterator<Integer> leftIterator = leftPartitions.iterator();
        if (leftIterator.hasNext())
            leftPartition = leftIterator.next();
        else
            leftPartition = 1; // arbitrary choice

        Set<Integer> rightPartitions = rightTerm.getPartitionsFromSymbols();
        rightPartitions.remove(-1);
        assert (rightPartitions.size() <= 1);
        int rightPartition;
        Iterator<Integer> rightIterator = rightPartitions.iterator();
        if (rightIterator.hasNext())
            rightPartition = rightIterator.next();
        else
            rightPartition = leftPartition; // arbitrary choice

        if (leftPartition == rightPartition) {
            // this is a local node
            TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(
                    leftPartition, rightPartition, this));

            for (int count = 0; count < subProofs.size(); count++) {
                assert (subProofs.get(count) instanceof TransformedZ3Proof);
                Z3Proof subProof = subProofs.get(count);
                AnnotatedProofNode currentAnnotatedNode = TransformedZ3Proof.annotatedNodes
                        .getNodeWithConsequent(subProof.consequent);
                if (currentAnnotatedNode.numPremises() == 3) {
                    List<TransformedZ3Proof> proofs = new ArrayList<TransformedZ3Proof>(
                            3);
                    proofs.add(currentAnnotatedNode.getPremise1());
                    proofs.add(currentAnnotatedNode.getPremise2());
                    proofs.add(currentAnnotatedNode.getPremise3());
                    Z3Proof newProof = TransformedZ3Proof
                            .createTransitivityProofForTransformedZ3Proofs(proofs);
                    subProofs.set(count, newProof);
                    TransformedZ3Proof.annotatedNodes
                            .add(new AnnotatedProofNode(leftPartition,
                                    leftPartition, this));
                }
            }
            return;
        }

        List<AnnotatedProofNode> currentAnnotatedNodes = new ArrayList<AnnotatedProofNode>();
        for (Z3Proof child : subProofs) {
            assert (child instanceof TransformedZ3Proof);
            Z3Proof subProof = child;
            AnnotatedProofNode currentAnnotatedNode = TransformedZ3Proof.annotatedNodes
                    .getNodeWithConsequent(subProof.consequent);
            assert (currentAnnotatedNode != null);
            currentAnnotatedNodes.add(currentAnnotatedNode);
        }

        List<DomainTerm> newLeftTerms = new ArrayList<DomainTerm>();
        List<DomainTerm> newRightTerms = new ArrayList<DomainTerm>();
        List<TransformedZ3Proof[]> proofs = new ArrayList<TransformedZ3Proof[]>();

        for (int count = 0; count < subProofs.size(); count++) {
            AnnotatedProofNode currentAnnotatedNode = TransformedZ3Proof.annotatedNodes
                    .getNodeWithConsequent(subProofs.get(count).consequent);
            DomainTerm[] oldTerms = Util.getDomainTerms(currentAnnotatedNode);
            DomainTerm currentLeftTerm = computeCurrentLeftTermForMonotonicity(
                    leftPartition, currentAnnotatedNode);
            newLeftTerms.add(currentLeftTerm);
            DomainTerm currentRightTerm = computeCurrentRightTermForMonotonicity(
                    rightPartition, currentAnnotatedNode);
            newRightTerms.add(currentRightTerm);

            TransformedZ3Proof newTransitivityProofNode = null;
            if (currentAnnotatedNode.numPremises() == 3) {
                DomainTerm[] currentTerms = Util
                        .getDomainTerms(currentAnnotatedNode);
                assert (currentTerms.length == 4);
                List<TransformedZ3Proof> currentSubProofs = new ArrayList<TransformedZ3Proof>();
                currentSubProofs
                        .add(currentTerms[0].equals(currentLeftTerm) ? currentAnnotatedNode
                                .getPremise1() : TransformedZ3Proof
                                .createReflexivityProof(currentLeftTerm));
                currentSubProofs.add(currentAnnotatedNode.getPremise2());
                currentSubProofs
                        .add(currentTerms[3].equals(currentRightTerm) ? currentAnnotatedNode
                                .getPremise3() : TransformedZ3Proof
                                .createReflexivityProof(currentRightTerm));
                newTransitivityProofNode = TransformedZ3Proof
                        .createTransitivityProofForTransformedZ3Proofs(currentSubProofs);
            }

            TransformedZ3Proof[] proofsForCurrentTerms = createProofForCurrentTerms(
                    oldTerms[0], currentLeftTerm,
                    oldTerms[oldTerms.length - 1], currentRightTerm,
                    newTransitivityProofNode, currentAnnotatedNode);
            assert (proofsForCurrentTerms.length == 3);
            proofs.add(proofsForCurrentTerms);
        }

        // create local monotonicity proofs
        List<TransformedZ3Proof> proofs1 = new ArrayList<TransformedZ3Proof>(
                proofs.size());
        List<TransformedZ3Proof> proofs2 = new ArrayList<TransformedZ3Proof>(
                proofs.size());
        List<TransformedZ3Proof> proofs3 = new ArrayList<TransformedZ3Proof>(
                proofs.size());
        for (TransformedZ3Proof[] currentProofs : proofs) {
            assert (currentProofs.length == 3);
            proofs1.add(currentProofs[0]);
            proofs2.add(currentProofs[1]);
            proofs3.add(currentProofs[2]);
        }
        UninterpretedFunction function = Util.getUninterpretedFunction(Util
                .getSingleLiteral(consequent));
        TransformedZ3Proof proof1 = TransformedZ3Proof.createMonotonicityProof(
                proofs1, function);
        TransformedZ3Proof proof2 = TransformedZ3Proof.createMonotonicityProof(
                proofs2, function);
        TransformedZ3Proof proof3 = TransformedZ3Proof.createMonotonicityProof(
                proofs3, function);

        // put things together, add new annotated node
        TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(
                leftPartition, rightPartition, this, proof1, proof2, proof3));
    }

    /**
     * Creates the new proof objects during monotonicity handling
     * 
     * @param leftTerm
     *            r_k
     * @param newLeftTerm
     *            r'_k
     * @param rightTerm
     *            s_k
     * @param newRightTerm
     *            s'_k
     * @param newProofNode
     *            proof for r'_k=s'_k, if there was a 3-premise annotated node
     *            as an antecedent. <code>null</code> otherwise.
     * @param annotatedNode
     *            the annotated antecedent node.
     * @return
     */
    private TransformedZ3Proof[] createProofForCurrentTerms(
            DomainTerm leftTerm, DomainTerm newLeftTerm, DomainTerm rightTerm,
            DomainTerm newRightTerm, TransformedZ3Proof newProofNode,
            AnnotatedProofNode annotatedNode) {

        TransformedZ3Proof[] result = new TransformedZ3Proof[3];
        result[0] = null;
        result[1] = null;
        result[2] = null;

        // result[0]
        if (leftTerm.equals(newLeftTerm))
            result[0] = TransformedZ3Proof.createReflexivityProof(newLeftTerm);
        else if (annotatedNode.numPremises() == 3)
            result[0] = annotatedNode.getPremise1();
        else
            result[0] = annotatedNode.getConsequent();

        // result[1]
        if (newLeftTerm.equals(newRightTerm))
            result[1] = TransformedZ3Proof.createReflexivityProof(newLeftTerm);

        if (annotatedNode.numPremises() == 3) {
            assert (newProofNode != null);
            result[1] = newProofNode;
        } else {
            assert (annotatedNode.numPremises() == 0);
            if (leftTerm.equals(newLeftTerm)) {
                assert (rightTerm.equals(newRightTerm));
                result[1] = annotatedNode.getConsequent();
            } else {
                assert (!rightTerm.equals(newRightTerm));
                result[1] = TransformedZ3Proof
                        .createSymmetryProof(annotatedNode.getConsequent());
            }
        }

        // result[2]
        if (rightTerm.equals(newRightTerm))
            result[2] = TransformedZ3Proof.createReflexivityProof(newRightTerm);
        else if (annotatedNode.numPremises() == 3)
            result[2] = annotatedNode.getPremise3();
        else
            result[2] = annotatedNode.getConsequent();

        return result;
    }

    /**
     * Computes the right term s'_k during monotonicity handling.
     * 
     * @param rightPartition
     * @param currentAnnotatedNode
     * @return
     */
    private DomainTerm computeCurrentRightTermForMonotonicity(
            int rightPartition, AnnotatedProofNode currentAnnotatedNode) {
        if (currentAnnotatedNode.getRightPartition() != rightPartition) {
            Formula formula = Util.getSingleLiteral(currentAnnotatedNode
                    .getConsequent().consequent);
            assert (formula instanceof DomainEq);
            DomainEq eqFormula = (DomainEq) formula;
            assert (eqFormula.getTerms().size() == 2);
            assert (eqFormula.getTerms().get(1) instanceof DomainTerm);
            return (DomainTerm) eqFormula.getTerms().get(1);
        } else if (currentAnnotatedNode.numPremises() == 3) {
            Formula formula = Util.getSingleLiteral(currentAnnotatedNode
                    .getPremise3().consequent);
            assert (formula instanceof DomainEq);
            DomainEq eqFormula = (DomainEq) formula;
            assert (eqFormula.getTerms().size() == 2);
            assert (eqFormula.getTerms().get(0) instanceof DomainTerm);
            return (DomainTerm) eqFormula.getTerms().get(0);
        } else {
            Formula formula = Util.getSingleLiteral(currentAnnotatedNode
                    .getConsequent().consequent);
            assert (formula instanceof DomainEq);
            DomainEq eqFormula = (DomainEq) formula;
            assert (eqFormula.getTerms().size() == 2);
            assert (eqFormula.getTerms().get(0) instanceof DomainTerm);
            return (DomainTerm) eqFormula.getTerms().get(0);
        }
    }

    /**
     * Computes the left term r'_k during monotonicity handling.
     * 
     * @param leftPartition
     * @param currentAnnotatedNode
     * @return
     */
    private DomainTerm computeCurrentLeftTermForMonotonicity(int leftPartition,
            AnnotatedProofNode currentAnnotatedNode) {

        if (currentAnnotatedNode.getLeftPartition() != leftPartition) {
            Formula formula = Util.getSingleLiteral(currentAnnotatedNode
                    .getConsequent().consequent);
            assert (formula instanceof DomainEq);
            DomainEq eqFormula = (DomainEq) formula;
            assert (eqFormula.getTerms().size() == 2);
            assert (eqFormula.getTerms().get(0) instanceof DomainTerm);
            return (DomainTerm) eqFormula.getTerms().get(0);
        } else if (currentAnnotatedNode.numPremises() == 3) {
            Formula formula = Util.getSingleLiteral(currentAnnotatedNode
                    .getPremise1().consequent);
            assert (formula instanceof DomainEq);
            DomainEq eqFormula = (DomainEq) formula;
            assert (eqFormula.getTerms().size() == 2);
            assert (eqFormula.getTerms().get(1) instanceof DomainTerm);
            return (DomainTerm) eqFormula.getTerms().get(1);
        } else {
            Formula formula = Util.getSingleLiteral(currentAnnotatedNode
                    .getConsequent().consequent);
            assert (formula instanceof DomainEq);
            DomainEq eqFormula = (DomainEq) formula;
            assert (eqFormula.getTerms().size() == 2);
            assert (eqFormula.getTerms().get(1) instanceof DomainTerm);
            return (DomainTerm) eqFormula.getTerms().get(1);
        }
    }

    /**
     * Deals with transforming a transitivity node to a local proof.
     */
    private void handleTransitivity() {
        // At this point, there should be only simple (2 subproof)
        // transitivities. 3-subproof transitivities may be added later (by
        // conversion from annotated nodes). Our transformation rules cannot
        // deal with 3-subproof transitivities at the moment, thus DO NOT REMOVE
        // THE FOLLOWING ASSERT!
        assert (subProofs.size() == 2);

        AnnotatedProofNode firstAnnotatedNode = TransformedZ3Proof.annotatedNodes
                .getNodeWithConsequent(subProofs.get(0).consequent);
        assert (firstAnnotatedNode != null);

        AnnotatedProofNode secondAnnotatedNode = TransformedZ3Proof.annotatedNodes
                .getNodeWithConsequent(subProofs.get(1).consequent);
        assert (secondAnnotatedNode != null);

        if (firstAnnotatedNode.numPremises() == 0
                && secondAnnotatedNode.numPremises() == 0) {
            if (firstAnnotatedNode.getPartition() == secondAnnotatedNode
                    .getPartition())
                handleTransitivityCase1(firstAnnotatedNode.getPartition());
            else
                handleTransitivityCase2(firstAnnotatedNode.getPartition(),
                        secondAnnotatedNode.getPartition());
        } else if (firstAnnotatedNode.numPremises() == 3
                && secondAnnotatedNode.numPremises() == 0) {
            if (firstAnnotatedNode.getRightPartition() == secondAnnotatedNode
                    .getPartition())
                handleTransitivityCase3(firstAnnotatedNode, secondAnnotatedNode);
            else
                handleTransitivityCase5(firstAnnotatedNode, secondAnnotatedNode);
        } else if (firstAnnotatedNode.numPremises() == 0
                && secondAnnotatedNode.numPremises() == 3) {
            if (firstAnnotatedNode.getLeftPartition() == secondAnnotatedNode
                    .getLeftPartition())
                handleTransitivityCase4(firstAnnotatedNode, secondAnnotatedNode);
            else
                handleTransitivityCase6(firstAnnotatedNode, secondAnnotatedNode);
        } else if (firstAnnotatedNode.numPremises() == 3
                && secondAnnotatedNode.numPremises() == 3) {
            handleTransitivityCase7(firstAnnotatedNode, secondAnnotatedNode);
        } else
            assert (false);
    }

    /**
     * Deals with the case that both equalities are from the same partition and
     * have annotated nodes with 0 premises.
     * 
     * @param partition
     *            the partition to which the new annotated node should be added
     */
    private void handleTransitivityCase1(int partition) {
        TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(partition,
                partition, this));
    }

    /**
     * Deals with the case that both equalities have annotated nodes with 0
     * premises, but from different partitions.
     * 
     * @param leftPartition
     * @param rightPartition
     * 
     */
    private void handleTransitivityCase2(int leftPartition, int rightPartition) {
        assert (Util
                .makeLiteralPositive(Util.getSingleLiteral(subProofs.get(0).consequent)) instanceof EqualityFormula);
        EqualityFormula formula = (EqualityFormula) Util
                .makeLiteralPositive(Util.getSingleLiteral(subProofs.get(0).consequent));
        assert (formula.getTerms().size() == 2);
        Term term = formula.getTerms().get(1);

        assert (Util
                .makeLiteralPositive(Util.getSingleLiteral(subProofs.get(1).consequent)) instanceof EqualityFormula);
        EqualityFormula formula2 = (EqualityFormula) Util
                .makeLiteralPositive(Util.getSingleLiteral(subProofs.get(1).consequent));
        assert (formula2.getTerms().size() == 2);
        Term term2 = formula2.getTerms().get(0);

        assert (term.equals(term2));

        TransformedZ3Proof reflexivity = TransformedZ3Proof
                .createReflexivityProof(term);
        TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(
                leftPartition, rightPartition, this,
                (TransformedZ3Proof) this.subProofs.get(0), reflexivity,
                (TransformedZ3Proof) this.subProofs.get(1)));
    }

    /**
     * Deals with the case that the first equalities has an annotated nodes with
     * 3 premises, the second one has an annotated node with 0 premises, and the
     * partition of the second node equals the right partition of the first
     * node.
     * 
     * @param firstAnnotatedNode
     * @param secondAnnotatedNode
     * 
     */
    private void handleTransitivityCase3(AnnotatedProofNode firstAnnotatedNode,
            AnnotatedProofNode secondAnnotatedNode) {
        List<TransformedZ3Proof> newSubProofs = new ArrayList<TransformedZ3Proof>(
                3);
        newSubProofs.add(firstAnnotatedNode.getPremise3());
        newSubProofs.add(secondAnnotatedNode.getConsequent());
        TransformedZ3Proof newProofNode = TransformedZ3Proof
                .createTransitivityProofForTransformedZ3Proofs(newSubProofs);
        assert (newProofNode.checkZ3ProofNode());
        TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(
                firstAnnotatedNode.getLeftPartition(), firstAnnotatedNode
                        .getRightPartition(), this, firstAnnotatedNode
                        .getPremise1(), firstAnnotatedNode.getPremise2(),
                newProofNode));
    }

    /**
     * Deals with the case that the first equalities has an annotated nodes with
     * 0 premises, the second one has an annotated node with 3 premises, and the
     * partition of the first node equals the left partition of the second node.
     * 
     * @param firstAnnotatedNode
     * @param secondAnnotatedNode
     * 
     */
    private void handleTransitivityCase4(AnnotatedProofNode firstAnnotatedNode,
            AnnotatedProofNode secondAnnotatedNode) {
        List<TransformedZ3Proof> newSubProofs = new ArrayList<TransformedZ3Proof>();
        newSubProofs.add(firstAnnotatedNode.getConsequent());
        newSubProofs.add(secondAnnotatedNode.getPremise1());
        TransformedZ3Proof newProofNode = TransformedZ3Proof
                .createTransitivityProofForTransformedZ3Proofs(newSubProofs);
        TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(
                firstAnnotatedNode.getPartition(), secondAnnotatedNode
                        .getRightPartition(), this, newProofNode,
                secondAnnotatedNode.getPremise2(), secondAnnotatedNode
                        .getPremise3()));

    }

    /**
     * Deals with the case that the first equalities has an annotated nodes with
     * 3 premises, the second one has an annotated node with 0 premises, and the
     * right partition of the first node is different from the partition of the
     * second node.
     * 
     * @param firstAnnotatedNode
     * @param secondAnnotatedNode
     * 
     */
    private void handleTransitivityCase5(AnnotatedProofNode firstAnnotatedNode,
            AnnotatedProofNode secondAnnotatedNode) {
        List<TransformedZ3Proof> newSubProofs = new ArrayList<TransformedZ3Proof>();
        newSubProofs.add(firstAnnotatedNode.getPremise2());
        newSubProofs.add(firstAnnotatedNode.getPremise3());
        TransformedZ3Proof newProofNode = TransformedZ3Proof
                .createTransitivityProofForTransformedZ3Proofs(newSubProofs);
        TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(
                firstAnnotatedNode.getLeftPartition(), secondAnnotatedNode
                        .getPartition(), this,
                firstAnnotatedNode.getPremise1(), newProofNode,
                secondAnnotatedNode.getConsequent()));

    }

    /**
     * Deals with the case that the first equalities has an annotated nodes with
     * 0 premises, the second one has an annotated node with 3 premises, and the
     * partition of the first node is different from the left partition of the
     * second node.
     * 
     * @param firstAnnotatedNode
     * @param secondAnnotatedNode
     * 
     */
    private void handleTransitivityCase6(AnnotatedProofNode firstAnnotatedNode,
            AnnotatedProofNode secondAnnotatedNode) {
        List<TransformedZ3Proof> newSubProofs = new ArrayList<TransformedZ3Proof>();
        newSubProofs.add(secondAnnotatedNode.getPremise1());
        newSubProofs.add(secondAnnotatedNode.getPremise2());
        TransformedZ3Proof newProofNode = TransformedZ3Proof
                .createTransitivityProofForTransformedZ3Proofs(newSubProofs);
        TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(
                firstAnnotatedNode.getPartition(), secondAnnotatedNode
                        .getRightPartition(), this, firstAnnotatedNode
                        .getConsequent(), newProofNode, secondAnnotatedNode
                        .getPremise3()));
    }

    /**
     * Deals with the case that both annotated nodes have 3 premises.
     * 
     * @param firstAnnotatedNode
     * @param secondAnnotatedNode
     */
    private void handleTransitivityCase7(AnnotatedProofNode firstAnnotatedNode,
            AnnotatedProofNode secondAnnotatedNode) {
        List<TransformedZ3Proof> newSubProofs1 = new ArrayList<TransformedZ3Proof>();
        newSubProofs1.add(firstAnnotatedNode.getPremise3());
        newSubProofs1.add(secondAnnotatedNode.getPremise1());
        TransformedZ3Proof newProofNode1 = TransformedZ3Proof
                .createTransitivityProofForTransformedZ3Proofs(newSubProofs1);

        List<TransformedZ3Proof> newSubProofs2 = new ArrayList<TransformedZ3Proof>();
        newSubProofs2.add(firstAnnotatedNode.getPremise2());
        newSubProofs2.add(newProofNode1);
        newSubProofs2.add(secondAnnotatedNode.getPremise2());
        TransformedZ3Proof newProofNode2 = TransformedZ3Proof
                .createTransitivityProofForTransformedZ3Proofs(newSubProofs2);

        TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(
                firstAnnotatedNode.getLeftPartition(), secondAnnotatedNode
                        .getRightPartition(), this, firstAnnotatedNode
                        .getPremise1(), newProofNode2, secondAnnotatedNode
                        .getPremise3()));
    }

    /**
     * 
     * @return A list of all leafs of this proof.
     */

    public List<TransformedZ3Proof> getLeafs() {

        int operationId = startDAGOperation();
        List<TransformedZ3Proof> result = this.getLeafsRecursion(operationId);
        endDAGOperation(operationId);

        return result;
    }

    public List<TransformedZ3Proof> getLeafsRecursion(int operationId) {
        visitedByDAGOperation(operationId);

        List<TransformedZ3Proof> result = new LinkedList<TransformedZ3Proof>();
        for (Z3Proof child : subProofs) {
            if (!(child instanceof TransformedZ3Proof))
                throw new RuntimeException(
                        "Base class z3Proof appears in tree of derived class TransformedZ3Proof. This should not happen!");
            TransformedZ3Proof subProof = (TransformedZ3Proof) child;

            if (subProof.isLeaf())
                result.add(subProof);
            else if (!subProof.wasVisitedByDAGOperation(operationId))
                result.addAll(subProof.getLeafsRecursion(operationId));
        }
        return result;
    }

    /**
     * 
     * @return <code>true</code> iff this proof object is a leaf.
     *         <code>false</code> otherwise.
     */
    public boolean isLeaf() {
        return subProofs.isEmpty();
    }

    /**
     * Creates a symmetry proof for the given premise.
     * 
     * @param premise
     *            must have a single literal as a consequence
     * @return a symmetry proof for the given premise.
     */
    public static TransformedZ3Proof createSymmetryProof(Z3Proof premise) {
        Z3Proof z3Proof = Z3Proof.createSymmetryProof(premise);
        List<TransformedZ3Proof> newSubProofs = new ArrayList<TransformedZ3Proof>(
                3);
        for (Z3Proof subProof : z3Proof.subProofs) {
            assert (subProof instanceof TransformedZ3Proof);
            newSubProofs.add((TransformedZ3Proof) subProof);
        }
        return new TransformedZ3Proof(z3Proof.proofType, newSubProofs,
                z3Proof.consequent);
    }

    /**
     * Creates a reflexivity proof for the given term.
     * 
     * @param term
     * @return a reflexivity proof for the given term.
     */
    public static TransformedZ3Proof createReflexivityProof(Term term) {

        List<Term> terms = new ArrayList<Term>();
        terms.add(term);
        terms.add(term);
        Formula formula = null;
        try {
            formula = EqualityFormula.create(terms, true);
        } catch (IncomparableTermsException exc) {
            throw new RuntimeException(
                    "Incomparable terms while creating reflexivity proof.", exc);
        }
        TransformedZ3Proof result = new TransformedZ3Proof(
                SExpressionConstants.ASSERTED,
                new ArrayList<TransformedZ3Proof>(), formula);
        result.axiom = true;
        return result;
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
    public static TransformedZ3Proof createTransitivityProofForTransformedZ3Proofs(
            List<TransformedZ3Proof> subProofs) {
        subProofs = new ArrayList<TransformedZ3Proof>(subProofs);
        assert (subProofs.size() == 2 || subProofs.size() == 3);
        if (subProofs.size() == 2) {
            assert (subProofs.size() == 2);
            Z3Proof z3Proof = Z3Proof.createTransitivityProof(subProofs);
            List<TransformedZ3Proof> newSubProofs = new ArrayList<TransformedZ3Proof>(
                    2);

            for (Z3Proof subProof : z3Proof.subProofs) {
                assert (subProof instanceof TransformedZ3Proof);
                newSubProofs.add((TransformedZ3Proof) subProof);
            }
            return new TransformedZ3Proof(z3Proof.proofType, newSubProofs,
                    z3Proof.consequent);
        } else {
            assert (subProofs.size() == 3);
            Z3Proof intermediate = Z3Proof
                    .createTransitivityProof(new ArrayList<Z3Proof>(subProofs
                            .subList(0, 2)));

            List<TransformedZ3Proof> intermediateSubProofs = new ArrayList<TransformedZ3Proof>(
                    2);
            for (Z3Proof subProof : intermediate.subProofs) {
                assert (subProof instanceof TransformedZ3Proof);
                intermediateSubProofs.add((TransformedZ3Proof) subProof);
            }
            TransformedZ3Proof transformedIntermediate = new TransformedZ3Proof(
                    intermediate.proofType, intermediateSubProofs,
                    intermediate.consequent);
            TransformedZ3Proof rest = subProofs.get(2);
            subProofs.clear();
            subProofs.add(transformedIntermediate);
            subProofs.add(rest);
            Z3Proof z3Proof = Z3Proof.createTransitivityProof(subProofs);
            List<TransformedZ3Proof> newSubProofs = new ArrayList<TransformedZ3Proof>(
                    3);
            for (Z3Proof subProof : z3Proof.subProofs) {
                assert (subProof instanceof TransformedZ3Proof);
                newSubProofs.add((TransformedZ3Proof) subProof);
            }
            return new TransformedZ3Proof(z3Proof.proofType, newSubProofs,
                    z3Proof.consequent);
        }

    }

    /**
     * Creates a monotonicity proof.
     * 
     * @param subProofs
     *            the equality proofs for the arguments
     * @param function
     *            the function which should be applied on the arguments
     * @return a monotonicity proof for the given parameters.
     */
    public static TransformedZ3Proof createMonotonicityProof(
            List<TransformedZ3Proof> subProofs, UninterpretedFunction function) {

        List<DomainTerm> leftParams = new ArrayList<DomainTerm>();
        List<DomainTerm> rightParams = new ArrayList<DomainTerm>();

        for (Z3Proof subProof : subProofs) {
            Formula literal = Util.getSingleLiteral(subProof.consequent);
            assert (literal instanceof DomainEq);
            DomainEq eqLiteral = (DomainEq) literal;
            assert (eqLiteral.getTerms().size() == 2);
            assert (eqLiteral.getTerms().get(0) instanceof DomainTerm);
            assert (eqLiteral.getTerms().get(1) instanceof DomainTerm);
            leftParams.add((DomainTerm) eqLiteral.getTerms().get(0));
            rightParams.add((DomainTerm) eqLiteral.getTerms().get(1));
        }

        EqualityFormula consequent = null;
        if (function.getType().equals(SExpressionConstants.VALUE_TYPE)) {
            try {
                UninterpretedFunctionInstance leftInstance = new UninterpretedFunctionInstance(
                        function, leftParams);
                UninterpretedFunctionInstance rightInstance = new UninterpretedFunctionInstance(
                        function, rightParams);
                List<DomainTerm> functionInstances = new ArrayList<DomainTerm>();
                functionInstances.add(leftInstance);
                functionInstances.add(rightInstance);
                consequent = EqualityFormula.create(functionInstances, true);
            } catch (WrongNumberOfParametersException exc) {
                throw new RuntimeException(
                        "Wrong number of function parameters while creating monotonicity proof.",
                        exc);
            } catch (WrongFunctionTypeException exc) {
                throw new RuntimeException(
                        "Wrong function type while creating monotonicity proof.",
                        exc);
            } catch (IncomparableTermsException exc) {
                throw new RuntimeException(
                        "Incomparable terms while creating monotonicity proof.",
                        exc);
            }
        } else {
            assert (function.getType().equals(SExpressionConstants.BOOL_TYPE));
            try {
                UninterpretedPredicateInstance leftInstance = new UninterpretedPredicateInstance(
                        function, leftParams);
                UninterpretedPredicateInstance rightInstance = new UninterpretedPredicateInstance(
                        function, rightParams);
                List<UninterpretedPredicateInstance> functionInstances = new ArrayList<UninterpretedPredicateInstance>();
                functionInstances.add(leftInstance);
                functionInstances.add(rightInstance);
                consequent = EqualityFormula.create(functionInstances, true);
            } catch (WrongNumberOfParametersException exc) {
                throw new RuntimeException(
                        "Wrong number of function parameters while creating monotonicity proof.",
                        exc);
            } catch (WrongFunctionTypeException exc) {
                throw new RuntimeException(
                        "Wrong function type while creating monotonicity proof.",
                        exc);
            } catch (IncomparableTermsException exc) {
                throw new RuntimeException(
                        "Incomparable terms while creating monotonicity proof.",
                        exc);
            }
        }
        TransformedZ3Proof result = new TransformedZ3Proof(
                SExpressionConstants.MONOTONICITY, subProofs, consequent);
        return result;
    }

    /**
     * @return the <code>literal</code>
     */
    public Formula getLiteral() {
        return literal;
    }

    /**
     * @return if is an axiom.
     */
    public boolean isAxiom() {
        return this.axiom;
    }

    /**
     * @return the <code>consequent</code>
     */
    @Override
    public Formula getConsequent() {
        return consequent;
    }

    /**
     * @return the <code>hypothesis</code>
     */
    public boolean isHypothesis() {
        return hypothesis || proofType.equals(SExpressionConstants.HYPOTHESIS);
    }

    /**
     * Computes the set of hypotheses on which this proof is based. Also, the
     * proof is on-the-fly restructured so that it has no more hypotheses.
     * 
     * @return The set of hypotheses that were removed from the proof.
     */
    private Set<Formula> removeHypotheses() {

        Set<Formula> result = new HashSet<Formula>();
        List<Z3Proof> hypotheses = new ArrayList<Z3Proof>(this.getHypotheses());
        Collections.sort(hypotheses);
        for (Z3Proof hypothesis : hypotheses) {
            assert (Util.isLiteral(hypothesis.consequent));
            result.add(hypothesis.consequent);

            // update the DAG with the negated literal
            Set<Z3Proof> nodes = nodesOnPathTo(hypothesis);
            Formula negatedLiteral = Util.invertLiteral(hypothesis.consequent);
            for (Z3Proof z3ProofNode : nodes) {
                // update the node.
                assert (z3ProofNode instanceof TransformedZ3Proof);
                TransformedZ3Proof node = (TransformedZ3Proof) z3ProofNode;

                assert (!node.isHypothesis());
                assert (node.consequent instanceof OrFormula);
                if (((OrFormula) node.consequent).getDisjuncts().contains(
                        negatedLiteral))
                    // Literal is already present. No need to add it.
                    continue;

                assert (node.subProofs.size() == 2);
                List<Formula> newDisjuncts = ((OrFormula) node.consequent)
                        .getDisjuncts();
                assert (!newDisjuncts.contains(negatedLiteral));
                newDisjuncts.remove(new PropositionalConstant(false));
                newDisjuncts.add(negatedLiteral);
                node.consequent = new OrFormula(newDisjuncts);

                if (node.subProofs.contains(hypothesis)) {
                    Z3Proof other = node.subProofs.get(node.subProofs
                            .indexOf(hypothesis) == 0 ? 1 : 0);
                    assert (other instanceof TransformedZ3Proof);
                    TransformedZ3Proof otherChild = (TransformedZ3Proof) other;
                    node.axiom = otherChild.axiom;
                    node.literal = otherChild.literal;
                    node.hypothesis = otherChild.hypothesis;
                    node.subProofs = otherChild.subProofs;
                    node.proofType = otherChild.proofType;
                }
            }
        }
        return result;
    }

    /**
     * Transforms a proof with transitivity, monotonicity, resolution and
     * symmetry into a pure resolution proof
     */
    public void toResolutionProof() {
        if (this.proofType.equals(SExpressionConstants.MONOTONICITY)
                || this.proofType.equals(SExpressionConstants.TRANSITIVITY)) {

            if (this.subProofs.size() < 1)
                throw new RuntimeException(
                        "Monotonicity/Transitivity proof with less than one child. This should not happen!");

            Set<Z3Proof> redundantSubproofs = new HashSet<Z3Proof>();
            for (Z3Proof subProof : this.subProofs) {
                if (Util.isReflexivity(subProof.consequent))
                    redundantSubproofs.add(subProof);
            }
            subProofs.removeAll(redundantSubproofs);

            List<Formula> axiomParts = new ArrayList<Formula>();
            for (Z3Proof subProof : this.subProofs) {
                axiomParts.add((new NotFormula(subProof.consequent))
                        .transformToConsequentsForm());
            }

            axiomParts.add(this.consequent);
            OrFormula axiomFormula = new OrFormula(axiomParts);

            Z3Proof remainingAxiom = new TransformedZ3Proof(
                    SExpressionConstants.ASSERTED,
                    new ArrayList<TransformedZ3Proof>(), null,
                    axiomFormula.transformToConsequentsForm());

            for (int count = 0; count < this.subProofs.size() - 1; count++) {

                TransformedZ3Proof currentEquality = (TransformedZ3Proof) this.subProofs
                        .get(count);
                currentEquality.toResolutionProof();
                axiomParts.remove(0);

                remainingAxiom = new TransformedZ3Proof(
                        SExpressionConstants.UNIT_RESOLUTION, currentEquality,
                        remainingAxiom, this.subProofs.get(count)
                                .getConsequent().transformToConsequentsForm(),
                        (new OrFormula(axiomParts))
                                .transformToConsequentsForm());
            }

            TransformedZ3Proof currentEquality = (TransformedZ3Proof) this.subProofs
                    .get(this.subProofs.size() - 1);
            currentEquality.toResolutionProof();

            this.subProofs = new ArrayList<Z3Proof>();
            this.subProofs.add(currentEquality);
            this.subProofs.add(remainingAxiom);

            this.literal = Util.getSingleLiteral(currentEquality
                    .getConsequent().transformToConsequentsForm());

            this.proofType = SExpressionConstants.UNIT_RESOLUTION;
            return;

        } else if (proofType.equals(SExpressionConstants.UNIT_RESOLUTION)) {
            for (Z3Proof child : subProofs) {
                assert (child instanceof TransformedZ3Proof);
                ((TransformedZ3Proof) child).toResolutionProof();
            }
            return;

        } else if (proofType.equals(SExpressionConstants.SYMMETRY)) {
            // Ignore symmetry. a=b and b=a should be treated as the
            // same object by later steps anyway.
            // NOTE (GH): Not sure if this is actually a correct assumption.

            if (this.subProofs.size() != 1)
                throw new RuntimeException(
                        "Symmetry proof with not exactly one child. This should not happen!");

            TransformedZ3Proof z3SubProof = (TransformedZ3Proof) this.subProofs
                    .get(0);
            z3SubProof.toResolutionProof();

            this.consequent = z3SubProof.consequent;
            this.subProofs = z3SubProof.subProofs;
            this.literal = Util.getSingleLiteral(z3SubProof.literal);
            this.proofType = z3SubProof.proofType;
            this.hypothesis = z3SubProof.hypothesis;
            this.axiom = z3SubProof.axiom;
            return;

        } else if (proofType.equals(SExpressionConstants.ASSERTED)) {
            return;

        } else {
            throw new RuntimeException("Encountered unexpected proof rule "
                    + proofType.toString()
                    + " while trying to rewrite z3 proof.");
        }
    }

    public static final ResProof createResolutionProof(
            Z3Proof transformedZ3Proof) {
        // TODO Auto-generated method stub
        return null;
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

        if (this.proofType == SExpressionConstants.UNIT_RESOLUTION) {
            if (this.literal != null) {
                String child = this.proofType
                        + "{"
                        + this.literal.toString().replaceAll("\n", "")
                                .replaceAll("\\s{2,}", " ") + "}";

                if (this.assertPartition != 0)
                    child += "(p:" + this.assertPartition + ")";

                children.add(new Token(child));
            }

            else
                throw new RuntimeException(
                        "resolution proof always needs a literal.");
        } else
            children.add(this.proofType);

        for (Z3Proof subProof : this.subProofs)
            children.add(subProof.toSmtlibV2());

        children.add(this.consequent.toSmtlibV2());
        return new SExpression(children);
    }

    /**
     * 
     * @return <code>true</code> if this is a local proof, <code>false</code> if
     *         it contains bad literals.
     */
    public boolean isLocal() {

        int operationId = startDAGOperation();
        boolean result = this.isLocalRecursion(operationId);
        endDAGOperation(operationId);

        return result;
    }

    private boolean isLocalRecursion(int operationId) {
        if (this.wasVisitedByDAGOperation(operationId))
            return true;
        visitedByDAGOperation(operationId);

        if (Util.containsBadLiteral((OrFormula) consequent))
            return false;

        for (Z3Proof child : subProofs) {
            if (child.wasVisitedByDAGOperation(operationId))
                continue;
            assert (child instanceof TransformedZ3Proof);
            if (!((TransformedZ3Proof) child).isLocal())
                return false;
        }
        return true;
    }

    public Map<PropositionalVariable, Formula> createITETrees(
            List<PropositionalVariable> ctrlSignals) {

        Map<PropositionalVariable, Formula> trees = new HashMap<PropositionalVariable, Formula>();

        // remove local parts of tree
        this.removeLocalPartsBeforeInterpolation();

        System.out.println("After removing local parts:");
        System.out.println("Proof DAG size: " + this.size(false));
        System.out
                .println("Proof size after unwinding DAG: " + this.size(true));

        // create ITE tree for each signal

        for (int signalNum = 0; signalNum < ctrlSignals.size(); signalNum++) {
            PropositionalVariable signal = ctrlSignals.get(signalNum);
            Formula tree = createITETree(signalNum);
            trees.put(signal, tree);
        }

        return trees;
    }

    public int getAssertPartition() {
        return this.assertPartition;
    }

    public void removeLocalPartsBeforeInterpolation() {
        // FIXME Don't unwind the DAG!
        if (this.proofType.equals(SExpressionConstants.UNIT_RESOLUTION)) {

            assert (this.literal != null);

            Set<Integer> literalPartitions = this.literal
                    .getPartitionsFromSymbols();
            assert (literalPartitions.size() == 1 || literalPartitions.size() == 2);
            literalPartitions.remove(-1);
            assert (literalPartitions.size() == 0 || literalPartitions.size() == 1);

            if (literalPartitions.size() == 1) {
                // This is resolution over a local literal.
                // ==> This node can be converted to ASSERTED
                // All descendants should only resolve on locals as well.
                // TODO: Check descendants!
                this.subProofs.clear();
                this.proofType = SExpressionConstants.ASSERTED;
                this.literal = null;
                this.assertPartition = literalPartitions.iterator().next();
            } else {
                // call recursive
                assert (subProofs.size() == 2);
                TransformedZ3Proof left = (TransformedZ3Proof) subProofs.get(0);
                TransformedZ3Proof right = (TransformedZ3Proof) subProofs
                        .get(1);

                left.removeLocalPartsBeforeInterpolation();
                right.removeLocalPartsBeforeInterpolation();
            }

        } else if (this.proofType.equals(SExpressionConstants.ASSERTED)) {
            return;
        } else
            throw new RuntimeException("encountered illegal proof type.");
    }

    private Formula createITETree(int signalNum) {

        // FIXME Don't unwind DAG!

        if (this.proofType == SExpressionConstants.UNIT_RESOLUTION) {

            // call recursive
            Formula leftResult = ((TransformedZ3Proof) subProofs.get(0))
                    .createITETree(signalNum);
            Formula rightResult = ((TransformedZ3Proof) subProofs.get(1))
                    .createITETree(signalNum);

            if (leftResult instanceof PropositionalConstant
                    && rightResult instanceof PropositionalConstant) {
                if (leftResult.equals(rightResult))
                    return leftResult;
            }

            // handle result of recursion
            OrFormula leftConsequent = ((OrFormula) subProofs.get(0)
                    .getConsequent());
            OrFormula rightConsequent = ((OrFormula) subProofs.get(1)
                    .getConsequent());

            if (checkPresence(leftConsequent, this.literal)) {
                if (!checkPresence(rightConsequent, this.literal)) {
                    // NOTE: Pudlak's "sel" works exactly opposite to "ite".
                    return new PropositionalIte(this.literal, rightResult,
                            leftResult);
                }
            } else if (!checkPresence(leftConsequent, this.literal)) {
                if (checkPresence(rightConsequent, this.literal)) {
                    // NOTE: Pudlak's "sel" works exactly opposite to "ite".
                    return new PropositionalIte(this.literal, leftResult,
                            rightResult);
                }
            } else
                throw new RuntimeException("found invalid unit-resolution.");
        } else if (this.proofType == SExpressionConstants.ASSERTED) {

            int partition = this.assertPartition;
            if (partition <= 0) {
                assert (partition == -1 || partition == 0);
                // this must be a "global clause", coming from an axiom
                // arbitrarily assign it to the first partition.
                partition = 1;
            }

            assert (partition > 0);
            BitSet bits = TransformedZ3Proof.bitSetFromLong(partition - 1);
            boolean isSet = bits.get(signalNum);

            return new PropositionalConstant(isSet);

        } else
            throw new RuntimeException(
                    "only resolution and asserted proof types allowed here.");
        return null;
    }

    public static BitSet bitSetFromLong(long value) {
        assert (value >= 0);
        BitSet bits = new BitSet();
        int index = 0;
        while (value != 0L) {
            if (value % 2L != 0) {
                bits.set(index);
            }
            ++index;
            value = value >>> 1;
        }
        return bits;
    }

    private boolean checkPresence(OrFormula haystack, Formula needle) {

        for (Formula disjunct : haystack.getDisjuncts()) {
            if (disjunct instanceof NotFormula) {// unwrap
                Formula tmp = ((NotFormula) disjunct).getNegatedFormula();
                if (tmp.equals(needle))
                    return false;
            } else {
                if (disjunct.equals(needle))
                    return true;
            }
        }

        throw new RuntimeException(
                "neither literal nor negated literal found! this should not happen!!");
    }

}