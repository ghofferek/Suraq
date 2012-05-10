/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
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
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
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
    private boolean axiom = false; // FIXME Do we really need this?

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

        if (proofType.equals(SExpressionConstants.ASSERTED)) {
            // This is a leave of the proof tree.
            assert (subProofs.size() == 0);

            this.proofType = z3Proof.getProofType();
            this.consequent = z3Proof.getConsequent()
                    .transformToConsequentsForm();

            return;

        } else if (proofType.equals(SExpressionConstants.AND_ELIM)
                || proofType.equals(SExpressionConstants.NOT_OR_ELIM)) {
            // Treat this as a leave.
            // Relies on the assumption that and-elim (not-or-elim) is only used
            // for things that have been asserted, and not on things are are
            // proven separately.

            assert (subProofs.size() == 0);

            this.proofType = (Token) SExpressionConstants.ASSERTED;
            this.consequent = z3Proof.getConsequent()
                    .transformToConsequentsForm();

            return;

        } else if (proofType.equals(SExpressionConstants.HYPOTHESIS)) {
            // Treat this as a leave.
            assert (subProofs.size() == 0);

            this.proofType = (Token) SExpressionConstants.ASSERTED;
            this.consequent = z3Proof.getConsequent()
                    .transformToConsequentsForm();
            this.hypothesis = true;

            return;

        } else if (proofType.equals(SExpressionConstants.AXIOM)
                || proofType.equals(SExpressionConstants.REFLEXIVITY)) {
            // Treat this as a leave.
            // It should be a propositional tautology.
            assert (subProofs.size() == 0);

            this.proofType = (Token) SExpressionConstants.ASSERTED;
            consequent = z3Proof.getConsequent().transformToConsequentsForm();

            axiom = true;

            return;

        } else if (proofType.equals(SExpressionConstants.MODUS_PONENS)) {

            List<Z3Proof> z3SubProofs = z3Proof.getSubProofs();
            if (z3SubProofs.size() != 2)
                throw new RuntimeException(
                        "Modus-Ponens proof with not exactly two children. This should not happen!");

            if (!(isLiteral(z3SubProofs.get(0).getConsequent())))
                throw new RuntimeException(
                        "First child of Modus-Ponens should be an Literal.");

            if (!(z3SubProofs.get(1).getConsequent() instanceof ImpliesFormula))
                throw new RuntimeException(
                        "Second child of Modus-Ponens should be an ImpliesFormla.");

            Z3Proof subProof2 = new Z3Proof(z3SubProofs.get(1).getProofType(),
                    z3SubProofs.get(1).getSubProofs(), z3SubProofs.get(1)
                            .getConsequent().transformToConsequentsForm());

            this.proofType = (Token) (SExpressionConstants.RESOLUTION);
            this.subProofs.add(new TransformedZ3Proof(z3SubProofs.get(0)));
            this.subProofs.add(new TransformedZ3Proof(subProof2));
            this.literal = makeLiteralPositive(z3SubProofs.get(0)
                    .getConsequent());
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
                        "Antecedent of Unit-Resolution proof is not an OrFormula. This should not happen.");

            OrFormula remainingFormula = (OrFormula) transformedAntecedent.consequent;

            for (int count = 1; count < z3SubProofs.size() - 1; count++) {
                List<Formula> newDisjuncts = remainingFormula.getDisjuncts();

                Formula resolutionAssociate = z3SubProofs.get(count)
                        .getConsequent();
                Formula invLiteral = invertLiteral(resolutionAssociate);
                Formula posLiteral = makeLiteralPositive(resolutionAssociate);

                newDisjuncts.remove(invLiteral);
                remainingFormula = new OrFormula(newDisjuncts);

                transformedAntecedent = new TransformedZ3Proof(
                        (Token) SExpressionConstants.RESOLUTION,
                        new TransformedZ3Proof(z3SubProofs.get(count)),
                        transformedAntecedent, posLiteral,
                        remainingFormula.transformToConsequentsForm());
            }

            this.proofType = (Token) SExpressionConstants.RESOLUTION;
            this.subProofs.add(new TransformedZ3Proof(z3SubProofs
                    .get(z3SubProofs.size() - 1)));
            this.subProofs.add(transformedAntecedent);

            Formula resolutionAssociate = z3SubProofs.get(
                    z3SubProofs.size() - 1).getConsequent();
            this.literal = makeLiteralPositive(resolutionAssociate);

            this.consequent = z3Proof.getConsequent();
            if (!(this.consequent instanceof PropositionalConstant))
                this.consequent = this.consequent.transformToConsequentsForm();

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
                this.consequent = z3Proof.getConsequent();
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
        this.computeParents(); // FIXME do we really need this?

        for (Z3Proof child : subProofs) {
            assert (child instanceof TransformedZ3Proof);
            TransformedZ3Proof subProof = (TransformedZ3Proof) child;
            subProof.toLocalProof();
        }

        // Recursive calls are completed. Now handle this particular node.

        if (!this.hasSingleLiteralConsequent())
            return; // Leave unchanged, this must be an intermediate resolution
                    // node.

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

            // TODO create proof nodes for annotated premises
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
        List<TransformedZ3Proof> newTransitivityProofNodes = new ArrayList<TransformedZ3Proof>();

        for (int count = 0; count < subProofs.size(); count++) {
            AnnotatedProofNode currentAnnotatedNode = TransformedZ3Proof.annotatedNodes
                    .getNodeWithConsequent(subProofs.get(count).consequent);

            DomainTerm currentLeftTerm = computeCurrentLeftTermForMonotonicity(
                    leftPartition, currentAnnotatedNode);
            DomainTerm currentRightTerm = computeCurrentRightTermForMonotonicity(
                    rightPartition, currentAnnotatedNode);

            // TODO create and add new terms, new transitivity proofs to lists
        }

        // TODO create local monotonicity proofs

        // TODO put thins together, add new annotated node

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
            if (isAtom(negatedFormula))
                return true;
        }
        if (isAtom(formula))
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
        assert (isAtom(literal));
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

        assert (isLiteral(literal));

        if (literal instanceof NotFormula) {
            return ((NotFormula) literal).getNegatedFormula();
        } else
            return new NotFormula(literal);
    }
}