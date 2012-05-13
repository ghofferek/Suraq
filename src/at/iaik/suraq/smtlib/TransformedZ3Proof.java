/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib;

import java.util.ArrayList;
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
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.FormulaTerm;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.util.Util;

/**
 * 
 * Should only contain the following proof rules: Asserted, Symmetry,
 * Transitivity, Monotonicity and (simple) Resolution.
 * 
 * Formulas for consequents should have the following structure: - each atom is
 * either a positive equality of two terms, a propositional variable, or an
 * uninterpreted predicate - each literal is either an atom or a negation of an
 * atom - formula is always an or formula which consists of at least one literal
 * 
 * Formulas for literals should be positive atoms as defined above.
 * 
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
public class TransformedZ3Proof extends Z3Proof {

    /**
     * A map from child nodes to parent nodes.
     */
    private static Map<TransformedZ3Proof, TransformedZ3Proof> parents = new HashMap<TransformedZ3Proof, TransformedZ3Proof>();

    /**
     * Specifies if this proof object is an axiom introduced during
     * transformation.
     */
    private boolean axiom = false;

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
     * Allows child to trigger restart of child recursion. Needed when child
     * changes parents subproofs.
     */
    private boolean reload = true;

    /**
     * Storage for annotated nodes used during proof conversion.
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

        this.literal = literal.deepFormulaCopy();
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
    public TransformedZ3Proof(Token proofType, TransformedZ3Proof subProof1,
            TransformedZ3Proof subProof2, Formula literal, Formula consequent) {

        super(proofType, subProof1, subProof2, consequent
                .transformToConsequentsForm().deepFormulaCopy());

        this.literal = literal.deepFormulaCopy();
    }

    public TransformedZ3Proof(Z3Proof z3Proof) {

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

            if (!(subProofs.size() == 0))
                throw new RuntimeException(
                        "Asserted Node should not have children");

            this.proofType = SExpressionConstants.ASSERTED;
            this.consequent = z3Proof.getConsequent()
                    .transformToConsequentsForm();

            return;

        } else if (proofType.equals(SExpressionConstants.HYPOTHESIS)) {
            // Treat this as a leave.
            if (!(subProofs.size() == 0))
                throw new RuntimeException(
                        "Asserted Node should not have children");

            this.proofType = SExpressionConstants.ASSERTED;
            this.consequent = z3Proof.getConsequent()
                    .transformToConsequentsForm();
            this.hypothesis = true;

            return;

        } else if (proofType.equals(SExpressionConstants.AXIOM)
                || proofType.equals(SExpressionConstants.REFLEXIVITY)) {
            // Treat this as a leave.
            // It should be a propositional tautology.
            if (!(subProofs.size() == 0))
                throw new RuntimeException(
                        "Asserted Node should not have children");

            this.proofType = SExpressionConstants.ASSERTED;
            consequent = z3Proof.getConsequent().transformToConsequentsForm();

            axiom = true;

            return;

        } else if (proofType.equals(SExpressionConstants.MODUS_PONENS)) {

            // Given a proof for p and a proof for (implies p q), produces a
            // proof for q. The second antecedents may also be a proof for (iff
            // p q).

            List<Z3Proof> z3SubProofs = z3Proof.getSubProofs();
            Z3Proof child0 = z3SubProofs.get(0);
            Z3Proof child1 = z3SubProofs.get(1);

            if (z3SubProofs.size() != 2)
                throw new RuntimeException(
                        "Modus-Ponens proof with not exactly two children. This should not happen!");

            if (!((child1.getConsequent() instanceof ImpliesFormula) || (child1
                    .getConsequent() instanceof EqualityFormula)))
                throw new RuntimeException(
                        "Second child of Modus-Ponens should be an ImpliesFormla or of the form (iff p q).");

            this.proofType = (SExpressionConstants.RESOLUTION);
            this.subProofs.add(new TransformedZ3Proof(child0));
            this.subProofs.add(new TransformedZ3Proof(child1));

            Formula newLiteral = z3SubProofs.get(0).getConsequent()
                    .transformToConsequentsForm();

            if (TransformedZ3Proof.isLiteral(newLiteral)) {
                this.literal = TransformedZ3Proof
                        .makeLiteralPositive(newLiteral);
            } else {
                if (newLiteral instanceof NotFormula)
                    throw new RuntimeException(
                            "Literal of modus ponens is a Not Formula. This should not happen.");

                Set<Integer> partitions = newLiteral.getAssertPartition();
                partitions.remove(-1);
                if (partitions.size() > 1)
                    throw new RuntimeException(
                            "First child of Modus-Ponens has more than one local assert-partition assigned."
                                    + newLiteral.toString());

                this.literal = new FormulaTerm(newLiteral);
            }

            this.literal = newLiteral;

            this.consequent = z3Proof.getConsequent()
                    .transformToConsequentsForm();

            return;

        } else if (proofType.equals(SExpressionConstants.UNIT_RESOLUTION)) {

            List<Z3Proof> z3SubProofs = z3Proof.getSubProofs();
            if (z3SubProofs.size() < 2)
                throw new RuntimeException(
                        "Unit-Resolution proof with less than two children. This should not happen!");

            TransformedZ3Proof transformedAntecedent = new TransformedZ3Proof(
                    z3SubProofs.get(0));

            if (!(transformedAntecedent.consequent instanceof OrFormula))
                throw new RuntimeException(
                        "Antecedent of Unit-Resolution proof is not an OrFormula. This should not happen."
                                + transformedAntecedent.consequent);

            OrFormula remainingFormula = (OrFormula) transformedAntecedent.consequent;

            for (int count = 1; count < z3SubProofs.size() - 1; count++) {
                List<Formula> newDisjuncts = remainingFormula.getDisjuncts();

                Formula resolutionAssociate = z3SubProofs.get(count)
                        .getConsequent();
                Formula invLiteral = TransformedZ3Proof
                        .invertLiteral(resolutionAssociate);
                Formula posLiteral = TransformedZ3Proof
                        .makeLiteralPositive(resolutionAssociate);

                newDisjuncts.remove(invLiteral);
                remainingFormula = new OrFormula(newDisjuncts);

                transformedAntecedent = new TransformedZ3Proof(
                        SExpressionConstants.RESOLUTION,
                        new TransformedZ3Proof(z3SubProofs.get(count)),
                        transformedAntecedent, posLiteral,
                        remainingFormula.transformToConsequentsForm());
            }

            this.proofType = SExpressionConstants.RESOLUTION;
            this.subProofs.add(new TransformedZ3Proof(z3SubProofs
                    .get(z3SubProofs.size() - 1)));
            this.subProofs.add(transformedAntecedent);

            Formula resolutionAssociate = z3SubProofs.get(
                    z3SubProofs.size() - 1).getConsequent();
            this.literal = TransformedZ3Proof
                    .makeLiteralPositive(resolutionAssociate);

            this.consequent = z3Proof.getConsequent();
            if (!(this.consequent instanceof PropositionalConstant))
                this.consequent = this.consequent.transformToConsequentsForm();

            return;

        } else if (proofType.equals(SExpressionConstants.LEMMA)) {
            List<Z3Proof> z3SubProofs = z3Proof.getSubProofs();
            if (z3SubProofs.size() != 1)
                throw new RuntimeException(
                        "Lemma proof with not exactly one child. This should not happen!");
            TransformedZ3Proof hypotheticalProof = new TransformedZ3Proof(
                    z3SubProofs.get(0));
            if (!hypotheticalProof.consequent.equals(new PropositionalConstant(
                    false)))
                throw new RuntimeException(
                        "Hypothetical proof (antecedent of lemma) does not prove false, but: "
                                + hypotheticalProof.consequent.toString());

            Map<TransformedZ3Proof, TransformedZ3Proof> parents = new HashMap<TransformedZ3Proof, TransformedZ3Proof>();
            hypotheticalProof.removeHypotheses(parents);

            this.proofType = hypotheticalProof.proofType;
            this.subProofs = hypotheticalProof.subProofs;
            this.consequent = hypotheticalProof.consequent;
            this.literal = hypotheticalProof.literal;
            return;

        } else {
            Token z3ProofType = z3Proof.getProofType();
            if (z3ProofType.equals(SExpressionConstants.TRANSITIVITY)
                    || z3ProofType.equals(SExpressionConstants.MONOTONICITY)
                    || z3ProofType.equals(SExpressionConstants.RESOLUTION)
                    || z3ProofType.equals(SExpressionConstants.SYMMETRY)) {

                this.proofType = z3ProofType;
                for (Z3Proof proof : z3Proof.getSubProofs()) {
                    this.subProofs.add(new TransformedZ3Proof(proof));
                }
                this.consequent = z3Proof.getConsequent()
                        .transformToConsequentsForm();
            } else {
                throw new RuntimeException("Encountered unexpected proof rule "
                        + proofType.toString()
                        + " while trying to rewrite z3 proof.");
            }
        }
    }

    /**
     * Transforms the proof into a local resolution proof (in place).
     */
    public void toLocalProof() {
        // this.computeParents(); // FIXME do we really need this?

        for (Z3Proof child : subProofs) {
            assert (child instanceof TransformedZ3Proof);
            TransformedZ3Proof subProof = (TransformedZ3Proof) child;
            subProof.toLocalProof();
        }

        // Recursive calls are completed. Now handle this particular node.

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

            // This must be an (intermediate) resolution node
            assert (this.proofType.equals(SExpressionConstants.UNIT_RESOLUTION));

            // Update subproofs
            assert (subProofs.size() == 2); // Multi-resolution should already
                                            // have been removed
            AnnotatedProofNode annotatedNode = TransformedZ3Proof.annotatedNodes
                    .getNodeWithConsequent(Util.getSingleLiteral(subProofs
                            .get(0).consequent));
            if (annotatedNode != null) {
                TransformedZ3Proof update = annotatedNode.getConsequent();
                if (annotatedNode.numPremises() == 3) {
                    List<TransformedZ3Proof> transSubProofs = new ArrayList<TransformedZ3Proof>(
                            3);
                    transSubProofs.add(annotatedNode.getPremise1());
                    transSubProofs.add(annotatedNode.getPremise2());
                    transSubProofs.add(annotatedNode.getPremise3());
                    update = TransformedZ3Proof
                            .createTransitivityProof(transSubProofs);
                }
                subProofs.set(0, update);
            }

            if (((TransformedZ3Proof) subProofs.get(1))
                    .hasSingleLiteralConsequent()) {
                AnnotatedProofNode annotatedNode2 = TransformedZ3Proof.annotatedNodes
                        .getNodeWithConsequent(Util.getSingleLiteral(subProofs
                                .get(1).consequent));
                TransformedZ3Proof update = annotatedNode.getConsequent();
                if (annotatedNode2.numPremises() == 3) {
                    List<TransformedZ3Proof> transSubProofs = new ArrayList<TransformedZ3Proof>(
                            3);
                    transSubProofs.add(annotatedNode2.getPremise1());
                    transSubProofs.add(annotatedNode2.getPremise2());
                    transSubProofs.add(annotatedNode2.getPremise3());
                    update = TransformedZ3Proof
                            .createTransitivityProof(transSubProofs);
                }
                subProofs.set(0, update);
            }
            return;
        }

        // All rules except unit-resolution should have single literal
        // consequents
        assert (this.hasSingleLiteralConsequent());
        // -------------------------------------------------------------
        if (this.proofType.equals(SExpressionConstants.ASSERTED)) {
            Formula literal = ((OrFormula) (this.consequent)).getDisjuncts()
                    .iterator().next();
            Set<Integer> partitions = literal.getAssertPartition();
            if (partitions.size() > 2)
                throw new RuntimeException(
                        "Asserted literal seems to come from more than one partitions. This should not happen!");
            int partition;
            Iterator<Integer> iterator = partitions.iterator();
            do {
                partition = iterator.next();
            } while (partition < 0);

            AnnotatedProofNode annotatedNode = new AnnotatedProofNode(
                    partition, partition, this, null, null, null);
            TransformedZ3Proof.annotatedNodes.add(annotatedNode);
            return;
        }

        // -------------------------------------------------------------
        if (this.proofType.equals(SExpressionConstants.SYMMETRY)) {
            assert (subProofs.size() == 1);
            TransformedZ3Proof subproof = (TransformedZ3Proof) subProofs.get(0);
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
                TransformedZ3Proof premise = (TransformedZ3Proof) this.subProofs
                        .get(0);
                assert (premise.hasSingleLiteralConsequent());
                TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(
                        annotatedNode.getPartition(), annotatedNode
                                .getPartition(), this, null, null, null));
            } else {
                assert (numPremises == 3);
                TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(
                        annotatedNode.getPartition(), annotatedNode
                                .getLeftPartition(), this, TransformedZ3Proof
                                .createSymmetrieProof(annotatedNode
                                        .getPremise1()), TransformedZ3Proof
                                .createSymmetrieProof(annotatedNode
                                        .getPremise2()), TransformedZ3Proof
                                .createSymmetrieProof(annotatedNode
                                        .getPremise3())));
            }
            return;
        }

        // -------------------------------------------------------------
        if (this.proofType.equals(SExpressionConstants.TRANSITIVITY)) {
            handleTransitivity();
            return;
        }

        // -------------------------------------------------------------
        if (this.proofType.equals(SExpressionConstants.MONOTONICITY)) {
            handleMonotonicity();
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

        Set<Integer> leftPartitions = leftTerm.getAssertPartition();
        assert (leftPartitions.size() <= 2);
        int leftPartition;
        Iterator<Integer> leftIterator = leftPartitions.iterator();
        do {
            leftPartition = leftIterator.next();
        } while (leftPartition < 0);

        Set<Integer> rightPartitions = rightTerm.getAssertPartition();
        assert (rightPartitions.size() <= 2);
        int rightPartition;
        Iterator<Integer> rightIterator = rightPartitions.iterator();
        do {
            rightPartition = rightIterator.next();
        } while (rightPartition < 0);

        if (leftPartition == rightPartition) {
            // this is a local node
            TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(
                    leftPartition, rightPartition, this));

            for (int count = 0; count < subProofs.size(); count++) {
                assert (subProofs.get(count) instanceof TransformedZ3Proof);
                TransformedZ3Proof subProof = (TransformedZ3Proof) subProofs
                        .get(count);
                AnnotatedProofNode currentAnnotatedNode = TransformedZ3Proof.annotatedNodes
                        .getNodeWithConsequent(subProof.consequent);
                if (currentAnnotatedNode.numPremises() == 3) {
                    List<TransformedZ3Proof> proofs = new ArrayList<TransformedZ3Proof>(
                            3);
                    proofs.add(currentAnnotatedNode.getPremise1());
                    proofs.add(currentAnnotatedNode.getPremise2());
                    proofs.add(currentAnnotatedNode.getPremise3());
                    TransformedZ3Proof newProof = TransformedZ3Proof
                            .createTransitivityProof(proofs);
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
            TransformedZ3Proof subProof = (TransformedZ3Proof) child;
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
                List<TransformedZ3Proof> currentSubProofs = new ArrayList<TransformedZ3Proof>();
                currentSubProofs
                        .add(leftTerm.equals(currentLeftTerm) ? currentAnnotatedNode
                                .getPremise1() : TransformedZ3Proof
                                .createReflexivityProof(leftTerm));
                currentSubProofs.add(currentAnnotatedNode.getPremise2());
                currentSubProofs
                        .add(rightTerm.equals(currentRightTerm) ? currentAnnotatedNode
                                .getPremise3() : TransformedZ3Proof
                                .createReflexivityProof(rightTerm));
                newTransitivityProofNode = TransformedZ3Proof
                        .createTransitivityProof(currentSubProofs);
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
                        .createSymmetrieProof(annotatedNode.getConsequent());
            }
        }

        // result[2]
        if (rightTerm.equals(newRightTerm))
            result[0] = TransformedZ3Proof.createReflexivityProof(newRightTerm);
        else if (annotatedNode.numPremises() == 3)
            result[0] = annotatedNode.getPremise3();
        else
            result[0] = annotatedNode.getConsequent();

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
            Formula formula = currentAnnotatedNode.getConsequent().consequent;
            assert (formula instanceof DomainEq);
            DomainEq eqFormula = (DomainEq) formula;
            assert (eqFormula.getTerms().size() == 2);
            assert (eqFormula.getTerms().get(1) instanceof DomainTerm);
            return (DomainTerm) eqFormula.getTerms().get(1);
        } else if (currentAnnotatedNode.numPremises() == 3) {
            Formula formula = currentAnnotatedNode.getPremise3().consequent;
            assert (formula instanceof DomainEq);
            DomainEq eqFormula = (DomainEq) formula;
            assert (eqFormula.getTerms().size() == 2);
            assert (eqFormula.getTerms().get(0) instanceof DomainTerm);
            return (DomainTerm) eqFormula.getTerms().get(0);
        } else {
            Formula formula = currentAnnotatedNode.getConsequent().consequent;
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
            Formula formula = currentAnnotatedNode.getConsequent().consequent;
            assert (formula instanceof DomainEq);
            DomainEq eqFormula = (DomainEq) formula;
            assert (eqFormula.getTerms().size() == 2);
            assert (eqFormula.getTerms().get(0) instanceof DomainTerm);
            return (DomainTerm) eqFormula.getTerms().get(0);
        } else if (currentAnnotatedNode.numPremises() == 3) {
            Formula formula = currentAnnotatedNode.getPremise1().consequent;
            assert (formula instanceof DomainEq);
            DomainEq eqFormula = (DomainEq) formula;
            assert (eqFormula.getTerms().size() == 2);
            assert (eqFormula.getTerms().get(1) instanceof DomainTerm);
            return (DomainTerm) eqFormula.getTerms().get(1);
        } else {
            Formula formula = currentAnnotatedNode.getConsequent().consequent;
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
    private void handleTransitivityCase2(int rightPartition, int leftPartition) {
        assert (subProofs.get(0).consequent instanceof EqualityFormula);
        EqualityFormula formula = (EqualityFormula) subProofs.get(0).consequent;
        assert (formula.getTerms().size() == 2);
        Term term = formula.getTerms().get(1);
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
     * right partition of the first node equals the partition of the second
     * node.
     * 
     * @param firstAnnotatedNode
     * @param secondAnnotatedNode
     * 
     */
    private void handleTransitivityCase3(AnnotatedProofNode firstAnnotatedNode,
            AnnotatedProofNode secondAnnotatedNode) {
        List<TransformedZ3Proof> newSubProofs = new ArrayList<TransformedZ3Proof>();
        newSubProofs.add(firstAnnotatedNode.getPremise3());
        newSubProofs.add(secondAnnotatedNode.getConsequent());
        TransformedZ3Proof newProofNode = TransformedZ3Proof
                .createTransitivityProof(newSubProofs);
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
                .createTransitivityProof(newSubProofs);
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
                .createTransitivityProof(newSubProofs);
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
                .createTransitivityProof(newSubProofs);
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
                .createTransitivityProof(newSubProofs1);

        List<TransformedZ3Proof> newSubProofs2 = new ArrayList<TransformedZ3Proof>();
        newSubProofs2.add(firstAnnotatedNode.getPremise2());
        newSubProofs2.add(newProofNode1);
        newSubProofs2.add(secondAnnotatedNode.getPremise2());
        TransformedZ3Proof newProofNode2 = TransformedZ3Proof
                .createTransitivityProof(newSubProofs2);

        TransformedZ3Proof.annotatedNodes.add(new AnnotatedProofNode(
                firstAnnotatedNode.getLeftPartition(), secondAnnotatedNode
                        .getRightPartition(), this, firstAnnotatedNode
                        .getPremise1(), newProofNode2, secondAnnotatedNode
                        .getPremise3()));
    }

    /**
     * @return <code>true</code> if the consequent of this node has only a
     *         single literal.
     */
    private boolean hasSingleLiteralConsequent() {
        OrFormula consequent = (OrFormula) this.consequent;
        return consequent.getDisjuncts().size() == 1;
    }

    /**
     * 
     * @return the parent of this node, if it is in the map, <code>null</code>
     *         otherwise.
     */
    public TransformedZ3Proof getParent() {
        return TransformedZ3Proof.parents.get(this);
    }

    /**
     * Recursively computes the parents in the proof, starting from
     * <code>this</code> downwards.
     */
    private void computeParents() {
        for (Z3Proof child : subProofs) {
            if (!(child instanceof TransformedZ3Proof))
                throw new RuntimeException(
                        "Base class z3Proof appears in tree of derived class TransformedZ3Proof. This should not happen!");
            TransformedZ3Proof.parents.put((TransformedZ3Proof) child, this);
            ((TransformedZ3Proof) child).computeParents();
        }
    }

    /**
     * 
     * @return A list of all leafs of this proof.
     */
    public List<TransformedZ3Proof> getLeafs() {
        List<TransformedZ3Proof> result = new LinkedList<TransformedZ3Proof>();
        for (Z3Proof child : subProofs) {
            if (!(child instanceof TransformedZ3Proof))
                throw new RuntimeException(
                        "Base class z3Proof appears in tree of derived class TransformedZ3Proof. This should not happen!");
            TransformedZ3Proof subProof = (TransformedZ3Proof) child;
            TransformedZ3Proof.parents.put(subProof, this);
            if (subProof.isLeaf())
                result.add(subProof);
            else
                result.addAll(subProof.getLeafs());
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
    public static TransformedZ3Proof createSymmetrieProof(
            TransformedZ3Proof premise) {
        assert (premise.hasSingleLiteralConsequent());
        Formula literal = ((OrFormula) (premise.consequent)).getDisjuncts()
                .iterator().next();
        assert (literal instanceof EqualityFormula);
        assert (((EqualityFormula) literal).isEqual());

        List<Term> terms = ((EqualityFormula) literal).getTerms();
        Collections.reverse(terms);
        Formula consequentFormula = null;
        try {
            consequentFormula = EqualityFormula.create(terms, true);
            consequentFormula = consequentFormula.transformToConsequentsForm();
            assert (consequentFormula != null);
        } catch (IncomparableTermsException exc) {
            throw new RuntimeException(
                    "Incomparable terms while creating symmetry proof.", exc);
        }
        List<TransformedZ3Proof> subproofs = new ArrayList<TransformedZ3Proof>();
        subproofs.add(premise);
        return new TransformedZ3Proof(SExpressionConstants.SYMMETRY, subproofs,
                consequentFormula);
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
                SExpressionConstants.REFLEXIVITY,
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
     * @return a reflexivity proof for the given term.
     */
    public static TransformedZ3Proof createTransitivityProof(
            List<TransformedZ3Proof> subProofs) {
        assert (subProofs.size() == 2 || subProofs.size() == 3);
        assert (subProofs.get(0).consequent instanceof EqualityFormula);
        assert (subProofs.get(1).consequent instanceof EqualityFormula);

        EqualityFormula firstFormula = (EqualityFormula) subProofs.get(0).consequent;
        EqualityFormula lastFormula = (EqualityFormula) subProofs.get(subProofs
                .size() - 1).consequent;

        assert (firstFormula.getTerms().size() == 2);
        Term term1 = firstFormula.getTerms().get(0);
        assert (lastFormula.getTerms().size() == 2);
        Term term2 = firstFormula.getTerms().get(1);

        List<Term> newTerms = new ArrayList<Term>();
        newTerms.add(term1);
        newTerms.add(term2);

        Formula newFormula = null;
        try {
            newFormula = EqualityFormula.create(newTerms, true);
        } catch (IncomparableTermsException exc) {
            throw new RuntimeException(
                    "Incomparable terms while creating transitivity proof.",
                    exc);
        }

        TransformedZ3Proof result = new TransformedZ3Proof(
                SExpressionConstants.TRANSITIVITY, subProofs, newFormula);
        return result;

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

        for (TransformedZ3Proof subProof : subProofs) {
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
        return hypothesis;
    }

    /**
     * Checks if a given Formula is an atom. An atom is either a
     * <code>EqualityFormula</code>, a <code>PropositionalVariable</code> or a
     * <code>UninterpretedPredicateInstance</code>.
     * 
     * @param formula
     *            formula to check
     * @return true, iff formula is atom
     * 
     */
    private static boolean isAtom(Formula formula) {
        if (formula instanceof EqualityFormula)
            return true;
        if (formula instanceof PropositionalVariable)
            return true;
        if (formula instanceof UninterpretedPredicateInstance)
            return true;

        return false;
    }

    /**
     * Checks if a given Formula is a literal. An literal is either an atom or a
     * negation of an atom.
     * 
     * @param formula
     *            formula to check
     * @return true, iff formula is literal
     * 
     */
    private static boolean isLiteral(Formula formula) {

        if (formula instanceof NotFormula) {
            Formula negatedFormula = ((NotFormula) formula).getNegatedFormula();
            if (TransformedZ3Proof.isAtom(negatedFormula))
                return true;
        }
        if (TransformedZ3Proof.isAtom(formula))
            return true;

        if (formula instanceof FormulaTerm)
            return true;

        return false;
    }

    /**
     * Removes negation from literal.
     * 
     * @param literal
     *            literal to make positive
     * @return the resulting atom
     * 
     */
    private static Formula makeLiteralPositive(Formula literal) {

        if (literal instanceof NotFormula) {
            literal = ((NotFormula) literal).getNegatedFormula();
        }
        assert (TransformedZ3Proof.isAtom(literal));
        return literal;
    }

    /**
     * Invert given literal.
     * 
     * @param literal
     *            literal to invert
     * @return the inverted literal
     * 
     */
    private static Formula invertLiteral(Formula literal) {

        assert (TransformedZ3Proof.isLiteral(literal));

        if (literal instanceof NotFormula) {
            return ((NotFormula) literal).getNegatedFormula();
        } else
            return new NotFormula(literal);
    }

    /**
     * Computes the set of hypotheses on which this proof is based. A map from
     * children to parents is constructed along the way. Also, the proof is
     * on-the-fly restructured so that it has no more hypotheses.
     * 
     * @param parents
     *            call-by-reference parameter for child->parent map.
     * @return The set of hypotheses that were removed from the proof.
     */
    private Set<Formula> removeHypotheses(
            Map<TransformedZ3Proof, TransformedZ3Proof> parents) {
        Set<Formula> result = new HashSet<Formula>();
        if (hypothesis) {
            // update ancestors' consequents
            TransformedZ3Proof parent = parents.get(this);

            while (parent != null) {
                List<Formula> newDisjuncts = null;
                if (parent.consequent instanceof OrFormula) {
                    newDisjuncts = ((OrFormula) parent.consequent)
                            .getDisjuncts();
                } else {
                    newDisjuncts = new ArrayList<Formula>();
                    newDisjuncts.add(parent.consequent);
                }
                newDisjuncts.add(new NotFormula(this.consequent));
                parent.consequent = (new OrFormula(newDisjuncts))
                        .transformToConsequentsForm();
                parent = parents.get(parent);
            }
            parent = parents.get(this);
            // update parent's subproofs and literal

            int numChildren = parent.subProofs.size();

            if (numChildren > 2) {
                parent.subProofs.remove(this);
                parent.reload = true;
            }
            if (numChildren == 2) {
                TransformedZ3Proof otherChild = (TransformedZ3Proof) parent.subProofs
                        .get((this == parent.subProofs.get(0)) ? 1 : 0);
                parent.proofType = otherChild.proofType;
                parent.subProofs = otherChild.subProofs;
                parent.literal = otherChild.literal;
                parent.hypothesis = otherChild.hypothesis;
                parent.reload = true;

            } else if (numChildren == 1) {

                TransformedZ3Proof myChild = this;
                TransformedZ3Proof myParent = parent;
                while (myParent.subProofs.size() == 1) {
                    myChild = myParent;
                    myParent = parents.get(myParent);
                }
                if (myParent.subProofs.size() > 2) {
                    myParent.subProofs.remove(myChild);
                    myParent.reload = true;
                }

                if (myParent.subProofs.size() == 2) {
                    TransformedZ3Proof otherChild = (TransformedZ3Proof) myParent.subProofs
                            .get((myChild == myParent.subProofs.get(0)) ? 1 : 0);
                    myParent.proofType = otherChild.proofType;
                    myParent.subProofs = otherChild.subProofs;
                    myParent.literal = otherChild.literal;
                    myParent.hypothesis = otherChild.hypothesis;
                    myParent.reload = true;
                }
            }

            result.add(consequent);
            return result;
        }

        reload = true;
        while (reload) {
            reload = false;
            for (Z3Proof subProof : subProofs) {
                if (subProof != null) {
                    parents.put((TransformedZ3Proof) subProof, this);
                    result.addAll(((TransformedZ3Proof) subProof)
                            .removeHypotheses(parents));
                    if (reload)
                        break;
                }
            }
        }

        return result;
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

        if (this.proofType == SExpressionConstants.RESOLUTION) {
            if (this.literal != null)
                children.add(new Token(this.proofType
                        + "{"
                        + this.literal.toString().replaceAll("\n", "")
                                .replaceAll("\\s{2,}", " ") + "}"));
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
}