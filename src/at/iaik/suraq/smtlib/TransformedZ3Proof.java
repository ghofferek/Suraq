/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
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
import at.iaik.suraq.resProof.Literal;
import at.iaik.suraq.resProof.ResNode;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.FormulaTerm;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.smtlib.formula.PropositionalEq;
import at.iaik.suraq.smtlib.formula.PropositionalIte;
import at.iaik.suraq.smtlib.formula.PropositionalTerm;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.util.DagOperationManager;
import at.iaik.suraq.util.ImmutableSet;
import at.iaik.suraq.util.TransitivityChainBuilder;
import at.iaik.suraq.util.Util;

/**
 * 
 * Should only contain the following proof rules: Asserted, Symmetry, (simple,
 * i.e., 2-subproof) Transitivity, Monotonicity and (simple, i.e. 2-subproof)
 * Resolution. Hypothesis-Lemma-Structures are also still allowed.
 * 
 * Formulas for consequents should have the following structure: - each atom is
 * either a positive equality of two terms, a propositional variable, or an
 * uninterpreted predicate - each literal is either an atom or a negation of an
 * atom - formula is always an or formula which consists of at least one literal
 * 
 * Formulas for literals should be positive atoms as defined above.
 * 
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>, Georg
 *         Hofferek <georg.hofferek@iaik.tugraz.at>
 */
public class TransformedZ3Proof extends Z3Proof {

    /**
     * 
     */
    private static final long serialVersionUID = -3623762531459362582L;

    @Deprecated
    public static TransformedZ3Proof debugNode = null;

    /**
     * This maps IDs of Z3Proofs to their TransformedZ3Proof counterparts. This
     * is to avoid DAG unwinding during conversion.
     */
    public static Map<Integer, TransformedZ3Proof> proofMap = new HashMap<Integer, TransformedZ3Proof>();

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
     * This flag stores whether this node has already been made local, at some
     * point in time.
     * 
     * Caveat: If something is changed in somewhere in the sub-graph below this
     * node, this flag might indicate the wrong value. Thus, be careful!
     */
    private boolean hasBeenMadeLocal = false;

    private static long numberOfRemovedObsoloteResolutionSteps = 0;

    /**
     * Storage for annotated nodes used during proof conversion.
     */
    private static Deque<AnnotatedProofNodes> annotatedNodesStack = new ArrayDeque<AnnotatedProofNodes>();

    /**
     * Counts how often the method <code>convertToTransformedZ3Proof</code> has
     * been called.
     */
    private static long conversionCounter = 0;

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
        this.recomputeObsoleteLiterals();
        this.computeHasBeenMadeLocal();

        assert (proofType.equals(SExpressionConstants.ASSERTED)
                || proofType.equals(SExpressionConstants.TRANSITIVITY)
                || proofType.equals(SExpressionConstants.SYMMETRY)
                || proofType.equals(SExpressionConstants.MONOTONICITY)
                || proofType.equals(SExpressionConstants.UNIT_RESOLUTION)
                || proofType.equals(SExpressionConstants.LEMMA) || proofType
                    .equals(SExpressionConstants.HYPOTHESIS));
        // if (this.id == 548)
        // this.checkZ3ProofNodeRecursive();
        // assert (this.checkZ3ProofNode());
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

        this.recomputeObsoleteLiterals();
        this.computeHasBeenMadeLocal();

        assert (literal == null || this.proofType
                .equals(SExpressionConstants.UNIT_RESOLUTION));
        assert (this.checkLiteralOccurenceInSubProofs());
        assert (proofType.equals(SExpressionConstants.ASSERTED)
                || proofType.equals(SExpressionConstants.TRANSITIVITY)
                || proofType.equals(SExpressionConstants.SYMMETRY)
                || proofType.equals(SExpressionConstants.MONOTONICITY) || proofType
                    .equals(SExpressionConstants.UNIT_RESOLUTION));
        // if (this.id == 548)
        // this.checkZ3ProofNodeRecursive();
        // assert (this.checkZ3ProofNode());
    }

    public TransformedZ3Proof(Token proofType,
            List<TransformedZ3Proof> subProofs, Formula consequent,
            int assertPartition, boolean axiom) {
        super(proofType, subProofs, consequent.transformToConsequentsForm()
                .deepFormulaCopy(), assertPartition, axiom);
        this.recomputeObsoleteLiterals();
        this.computeHasBeenMadeLocal();

        assert (proofType.equals(SExpressionConstants.ASSERTED)
                || proofType.equals(SExpressionConstants.TRANSITIVITY)
                || proofType.equals(SExpressionConstants.SYMMETRY)
                || proofType.equals(SExpressionConstants.MONOTONICITY) || proofType
                    .equals(SExpressionConstants.UNIT_RESOLUTION));
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

        this.literal = literal == null ? null : Util.makeLiteralPositive(Util
                .getSingleLiteral(literal.deepFormulaCopy()));
        this.recomputeObsoleteLiterals();
        this.computeHasBeenMadeLocal();

        assert (proofType.equals(SExpressionConstants.ASSERTED)
                || proofType.equals(SExpressionConstants.TRANSITIVITY)
                || proofType.equals(SExpressionConstants.SYMMETRY)
                || proofType.equals(SExpressionConstants.MONOTONICITY) || proofType
                    .equals(SExpressionConstants.UNIT_RESOLUTION));
        // if (this.id == 548 || subProof1.id == 548 || subProof2.id == 548)
        // this.checkZ3ProofNodeRecursive();
        // assert (this.checkZ3ProofNode());
    }

    public TransformedZ3Proof(ResNode node, Map<Integer, Formula> literalMap,
            Map<ResNode, TransformedZ3Proof> cache) {

        assert (cache != null);
        assert (!cache.containsKey(node));

        if (!node.isLeaf()) { // CREATE RESOLUTION NODE

            this.proofType = SExpressionConstants.UNIT_RESOLUTION;
            this.literal = literalMap.get(node.getPivot());

            TransformedZ3Proof left = cache.get(node.getLeft());
            this.subProofs.add(left == null ? new TransformedZ3Proof(node
                    .getLeft(), literalMap, cache) : left);

            TransformedZ3Proof right = cache.get(node.getRight());
            this.subProofs.add(right == null ? new TransformedZ3Proof(node
                    .getRight(), literalMap, cache) : right);
        } else { // CREATE ASSERTED NODE

            this.proofType = SExpressionConstants.ASSERTED;
        }

        // build consequent from clause
        List<Formula> disjuncts = new ArrayList<Formula>();
        for (Literal literal : node.getClause()) {
            Formula elem = literalMap.get(literal.id());
            if (!literal.isPos())
                elem = NotFormula.create(elem);
            disjuncts.add(elem);
        }

        if (disjuncts.size() == 0)
            disjuncts.add(PropositionalConstant.create(false));

        this.consequent = (OrFormula.generate(disjuncts))
                .transformToConsequentsForm();

        // this.recomputeObsoleteLiterals(); // What's this for??

        // TODO Check: Should this be set for leafs only?
        // assign global clauses to part 1 (arbitrary choice)
        this.assertPartition = node.getPart() == 0 ? 1 : node.getPart();

        assert (proofType.equals(SExpressionConstants.ASSERTED) || proofType
                .equals(SExpressionConstants.UNIT_RESOLUTION));

        assert (this.assertPartition > 0 || !this.proofType
                .equals(SExpressionConstants.ASSERTED));

        cache.put(node, this);
    }

    private void computeHasBeenMadeLocal() {

        if (subProofs.size() == 0) {
            // Leafs must be marked false at construction time.
            this.hasBeenMadeLocal = false;
            return;
        }

        if (Util.containsBadLiteral(this.consequent
                .transformToConsequentsForm())) {
            this.hasBeenMadeLocal = false;
            return;
        }
        for (Z3Proof child : subProofs) {
            assert (child instanceof TransformedZ3Proof);
            if (!((TransformedZ3Proof) child).hasBeenMadeLocal) {
                this.hasBeenMadeLocal = false;
                return;
            }
        }

        this.hasBeenMadeLocal = true;

        if (this.hasSingleLiteralConsequent()) {
            TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                    new AnnotatedProofNode(this));
        }

        return;
    }

    @Override
    protected void takeValuesFrom(Z3Proof proof) {
        assert (proof instanceof TransformedZ3Proof);
        super.takeValuesFrom(proof);
        TransformedZ3Proof transformedProof = (TransformedZ3Proof) proof;
        this.literal = transformedProof.literal == null ? null
                : transformedProof.literal.deepFormulaCopy();
        this.hypothesis = transformedProof.hypothesis;
        this.obsoleteLiterals = transformedProof.obsoleteLiterals;
        this.hasBeenMadeLocal = transformedProof.hasBeenMadeLocal;
    }

    public static TransformedZ3Proof convertToTransformedZ3Proof(Z3Proof z3Proof) {

        TransformedZ3Proof.conversionCounter++;

        if (TransformedZ3Proof.conversionCounter % 1000 == 0) {
            System.out
                    .println("PROGRESS-INFO: Conversion counter is at "
                            + Z3Proof.myFormatter
                                    .format(TransformedZ3Proof.conversionCounter)
                            + ".");
            System.out.println("PROGRESS-INFO: proofMap contains "
                    + Z3Proof.myFormatter.format(TransformedZ3Proof.proofMap
                            .size()) + " nodes.");
        }

        // TransformedZ3Proof.debugNode = TransformedZ3Proof.proofMap.get(307);

        if (TransformedZ3Proof.proofMap.containsKey(z3Proof.id))
            return TransformedZ3Proof.proofMap.get(z3Proof.id);
        // TransformedZ3Proof.proofMap.remove(z3Proof.id);

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

            assert (z3Proof.subProofs.size() == 0);

            if (z3Proof instanceof TransformedZ3Proof)
                return (TransformedZ3Proof) z3Proof;

            TransformedZ3Proof result = new TransformedZ3Proof(
                    SExpressionConstants.ASSERTED,
                    new ArrayList<TransformedZ3Proof>(), z3Proof
                            .getConsequent().transformToConsequentsForm());
            if (z3Proof.assertPartition > 0)
                result.assertPartition = z3Proof.assertPartition;

            assert (!TransformedZ3Proof.proofMap.containsKey(z3Proof.id));
            TransformedZ3Proof.proofMap.put(z3Proof.id, result);
            return result;

        } else if (proofType.equals(SExpressionConstants.HYPOTHESIS)) {
            // Treat this as a leave.
            assert (z3Proof.subProofs.isEmpty());

            TransformedZ3Proof result = new TransformedZ3Proof(
                    SExpressionConstants.ASSERTED,
                    new ArrayList<TransformedZ3Proof>(), z3Proof
                            .getConsequent().transformToConsequentsForm());
            result.hypothesis = true;
            result.obsoleteLiterals = result.obsoleteLiterals
                    .addAllToCopy(z3Proof.obsoleteLiterals);
            assert (!TransformedZ3Proof.proofMap.containsKey(z3Proof.id));
            TransformedZ3Proof.proofMap.put(z3Proof.id, result);
            return result;

        } else if (proofType.equals(SExpressionConstants.AXIOM)
                || proofType.equals(SExpressionConstants.REFLEXIVITY)) {
            // Treat this as a leave.
            // It should be a propositional tautology.
            assert (z3Proof.subProofs.isEmpty());

            TransformedZ3Proof result = new TransformedZ3Proof(
                    SExpressionConstants.ASSERTED,
                    new ArrayList<TransformedZ3Proof>(), z3Proof
                            .getConsequent().transformToConsequentsForm());
            if (z3Proof.assertPartition > 0)
                result.assertPartition = z3Proof.assertPartition;
            result.axiom = true;
            result.obsoleteLiterals = result.obsoleteLiterals
                    .addAllToCopy(z3Proof.obsoleteLiterals);
            assert (!TransformedZ3Proof.proofMap.containsKey(z3Proof.id));
            TransformedZ3Proof.proofMap.put(z3Proof.id, result);
            return result;

        } else if (proofType.equals(SExpressionConstants.MODUS_PONENS)) {

            // Recursive conversion calls will be done inside
            // handleModusPonens(Z3Proof).
            assert (!TransformedZ3Proof.proofMap.containsKey(z3Proof.id));
            TransformedZ3Proof result = TransformedZ3Proof
                    .convertModusPonens(z3Proof);
            assert (result.getConsequent().equals(z3Proof.getConsequent()
                    .transformToConsequentsForm()));
            result.obsoleteLiterals = result.obsoleteLiterals
                    .addAllToCopy(z3Proof.obsoleteLiterals);
            TransformedZ3Proof.proofMap.put(z3Proof.id, result);
            return result;

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

                remainingFormula = (OrFormula.generate(newDisjuncts))
                        .transformToConsequentsForm();

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
            result.obsoleteLiterals = result.obsoleteLiterals
                    .addAllToCopy(z3Proof.obsoleteLiterals);
            TransformedZ3Proof.proofMap.put(z3Proof.id, result);
            return result;

        } else if (proofType.equals(SExpressionConstants.LEMMA)) {

            List<Z3Proof> z3SubProofs = z3Proof.getSubProofs();
            if (z3SubProofs.size() != 1)
                throw new RuntimeException(
                        "Lemma proof with not exactly one child. This should not happen!");

            Z3Proof hypotheticalProof = z3SubProofs.get(0);

            // assert (hypotheticalProof.checkZ3ProofNodeRecursive());
            // hypotheticalProof.removeLocalSubProofs(); // redundant with call
            // in main (on main proof)?

            // assert (hypotheticalProof.checkZ3ProofNodeRecursive());
            TransformedZ3Proof transformedHypotheticalProof = TransformedZ3Proof
                    .convertToTransformedZ3Proof(hypotheticalProof);

            List<TransformedZ3Proof> list = new ArrayList<TransformedZ3Proof>(1);
            list.add(transformedHypotheticalProof);
            TransformedZ3Proof result = new TransformedZ3Proof(
                    SExpressionConstants.LEMMA, list,
                    z3Proof.consequent.deepFormulaCopy());
            result.obsoleteLiterals = result.obsoleteLiterals
                    .addAllToCopy(z3Proof.obsoleteLiterals);
            assert (!TransformedZ3Proof.proofMap.containsKey(z3Proof.id));
            TransformedZ3Proof.proofMap.put(z3Proof.id, result);
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
            current1.obsoleteLiterals = current1.obsoleteLiterals
                    .addAllToCopy(z3Proof.obsoleteLiterals);
            TransformedZ3Proof.proofMap.put(z3Proof.id, current1);
            return current1;

        } else if (proofType.equals(SExpressionConstants.SYMMETRY)) {

            List<TransformedZ3Proof> subProofs = new ArrayList<TransformedZ3Proof>();
            for (Z3Proof proof : z3Proof.subProofs) {
                subProofs.add(TransformedZ3Proof
                        .convertToTransformedZ3Proof(proof));
            }
            TransformedZ3Proof result = new TransformedZ3Proof(proofType,
                    subProofs, z3Proof.getConsequent()
                            .transformToConsequentsForm());
            assert (!TransformedZ3Proof.proofMap.containsKey(z3Proof.id));
            result.obsoleteLiterals = result.obsoleteLiterals
                    .addAllToCopy(z3Proof.obsoleteLiterals);
            TransformedZ3Proof.proofMap.put(z3Proof.id, result);
            return result;
        } else if (proofType.equals(SExpressionConstants.MONOTONICITY)) {

            // Add missing reflexivity proofs. Having them makes some
            // intermediate step easier, although they are removed later on.
            z3Proof.addMissingReflexivityProofs();
            List<TransformedZ3Proof> subProofs = new ArrayList<TransformedZ3Proof>();
            for (Z3Proof proof : z3Proof.subProofs) {
                subProofs.add(TransformedZ3Proof
                        .convertToTransformedZ3Proof(proof));
            }
            TransformedZ3Proof result = new TransformedZ3Proof(proofType,
                    subProofs, z3Proof.getConsequent()
                            .transformToConsequentsForm());
            assert (!TransformedZ3Proof.proofMap.containsKey(z3Proof.id));
            result.obsoleteLiterals = result.obsoleteLiterals
                    .addAllToCopy(z3Proof.obsoleteLiterals);
            TransformedZ3Proof.proofMap.put(z3Proof.id, result);
            return result;
        } else {
            throw new RuntimeException("Encountered unexpected proof rule "
                    + proofType.toString()
                    + " while trying to rewrite z3 proof.");
        }
    }

    public AnnotatedProofNodes toLocalProof() {
        return this.toLocalProof(null);
    }

    public AnnotatedProofNodes toLocalProof(String operationName) {

        // Actually, stack seems not to be needed.
        // To avoid refactoring, just don't add a new frame,
        // if there already is one.
        if (TransformedZ3Proof.annotatedNodesStack.size() < 1)
            TransformedZ3Proof.annotatedNodesStack
                    .addFirst(new AnnotatedProofNodes());
        assert (TransformedZ3Proof.annotatedNodesStack.size() == 1);

        long operationId = operationName != null ? DagOperationManager
                .startDAGOperation(operationName) : DagOperationManager
                .startDAGOperation();
        if (operationName != null)
            DagOperationManager.setMessageInterval(operationId, 100);

        this.toLocalProofRecursion(operationId);
        DagOperationManager.endDAGOperation(operationId);

        return TransformedZ3Proof.annotatedNodesStack.peekFirst();
    }

    /**
     * Transforms the proof into a local resolution proof (in place).
     */
    private void toLocalProofRecursion(long operationId) {

        if (this.wasVisitedByDAGOperation(operationId)) {
            // The fact that this node was visited does not imply that it is now
            // local. It could have been "detached" from the branch by which it
            // was visited, because, e.g., it contains a bad literal.
            return;
        }
        if (this.hasBeenMadeLocal) {
            // Do a quick, sound, but non-complete check
            // At least, the direct parents must also have the flag set.
            for (Z3Proof child : subProofs) {
                assert (child instanceof TransformedZ3Proof);
                assert (((TransformedZ3Proof) child).hasBeenMadeLocal);
            }
            visitedByDAGOperation(operationId);
            return;
        }

        visitedByDAGOperation(operationId);

        if (obsoleteLiterals == null)
            obsoleteLiterals = ImmutableSet.create(new HashSet<Formula>());

        for (int count = 0; count < subProofs.size(); count++) {
            Z3Proof child = subProofs.get(count);
            assert (child instanceof TransformedZ3Proof);
            TransformedZ3Proof subProof = (TransformedZ3Proof) child;
            subProof.toLocalProofRecursion(operationId);

            if (subProof.hasSingleLiteralConsequent()
                    && !this.proofType.equals(SExpressionConstants.LEMMA)) {
                // Use a localized version of this subproof

                Set<Formula> newObsoleteLiterals = new HashSet<Formula>();
                TransformedZ3Proof update = TransformedZ3Proof.annotatedNodesStack
                        .peekFirst()
                        .getNodeWithConsequent(subProof.consequent,
                                subProof.getHypothesisFormulas(),
                                newObsoleteLiterals).getConsequent();

                if (subProof != update) {
                    subProof.removeParent(this);
                    this.subProofs.set(count, update);
                    update.addParent(this);
                    Z3Proof.hypModCount++;
                    this.markHypCacheDirty();
                    this.obsoleteLiterals = this.obsoleteLiterals
                            .addAllToCopy(newObsoleteLiterals);
                }
            }

            assert (obsoleteLiterals != null);
            obsoleteLiterals = obsoleteLiterals
                    .addAllToCopy(subProof.obsoleteLiterals);
        }

        // Recursive calls are completed. Now handle this particular node.

        // -------------------------------------------------------------
        if (this.proofType.equals(SExpressionConstants.LEMMA)) {
            // Nothing more to do for lemmas with multiple-literal consequents.
            if (!this.hasSingleLiteralConsequent()) {
                assert (!Util.containsBadLiteral(this.consequent
                        .transformToConsequentsForm()));
                this.setHasBeenMadeLocal();
                return;
            }
        }
        // -------------------------------------------------------------
        if (this.proofType.equals(SExpressionConstants.SYMMETRY)) {
            assert (this.hasSingleLiteralConsequent());
            assert (subProofs.size() == 1);
            handleSymmetry();
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

            if (!(this.proofType.equals(SExpressionConstants.UNIT_RESOLUTION) || this.proofType
                    .equals(SExpressionConstants.ASSERTED)))
                assert (false);

            if (this.proofType.equals(SExpressionConstants.UNIT_RESOLUTION)) {
                // Update subproofs
                assert (subProofs.size() == 2); // Multi-resolution should
                                                // already have been removed

                assert (Util.checkResolutionNodeForBadLiterals(this));

                if (Util.isLiteral(subProofs.get(0).consequent)) {
                    Set<Formula> newObsoleteLiterals = new HashSet<Formula>();
                    AnnotatedProofNode annotatedNode = TransformedZ3Proof.annotatedNodesStack
                            .peekFirst()
                            .getNodeWithConsequent(
                                    Util.getSingleLiteral(subProofs.get(0).consequent),
                                    subProofs.get(0).getHypothesisFormulas(),
                                    newObsoleteLiterals);
                    if (annotatedNode != null) {
                        TransformedZ3Proof update = annotatedNode
                                .getConsequent();
                        if (annotatedNode.numPremises() == 3) {
                            List<TransformedZ3Proof> transSubProofs = new ArrayList<TransformedZ3Proof>(
                                    3);
                            transSubProofs.add(annotatedNode.getPremise1());
                            transSubProofs.add(annotatedNode.getPremise2());
                            transSubProofs.add(annotatedNode.getPremise3());
                            update = TransformedZ3Proof
                                    .createTransitivityProofForTransformedZ3Proofs(transSubProofs);
                            TransformedZ3Proof.annotatedNodesStack.peekFirst()
                                    .add(new AnnotatedProofNode(update));
                            update.obsoleteLiterals = update.obsoleteLiterals
                                    .addAllToCopy(newObsoleteLiterals);
                        }
                        // Too expensive?
                        // assert (((TransformedZ3Proof) update).isLocal());

                        if (subProofs.get(0) != update) {
                            subProofs.get(0).removeParent(this);
                            subProofs.set(0, update);
                            update.addParent(this);
                            Z3Proof.hypModCount++;
                            this.markHypCacheDirty();
                            recomputeObsoleteLiterals();
                        }

                    }
                }

                if (Util.isLiteral(subProofs.get(1).consequent)) {
                    Set<Formula> newObsoleteLiterals = new HashSet<Formula>();
                    AnnotatedProofNode annotatedNode2 = TransformedZ3Proof.annotatedNodesStack
                            .peekFirst()
                            .getNodeWithConsequent(
                                    Util.getSingleLiteral(subProofs.get(1).consequent),
                                    subProofs.get(1).getHypothesisFormulas(),
                                    newObsoleteLiterals);
                    if (annotatedNode2 != null) {
                        TransformedZ3Proof update = annotatedNode2
                                .getConsequent();
                        if (annotatedNode2.numPremises() == 3) {
                            List<TransformedZ3Proof> transSubProofs = new ArrayList<TransformedZ3Proof>(
                                    3);
                            transSubProofs.add(annotatedNode2.getPremise1());
                            transSubProofs.add(annotatedNode2.getPremise2());
                            transSubProofs.add(annotatedNode2.getPremise3());
                            update = TransformedZ3Proof
                                    .createTransitivityProofForTransformedZ3Proofs(transSubProofs);
                            TransformedZ3Proof.annotatedNodesStack.peekFirst()
                                    .add(new AnnotatedProofNode(update));
                            update.obsoleteLiterals = update.obsoleteLiterals
                                    .addAllToCopy(newObsoleteLiterals);
                        }
                        // Too expensive?
                        // assert (((TransformedZ3Proof) update).isLocal());

                        if (subProofs.get(1) != update) {
                            subProofs.get(1).removeParent(this);
                            subProofs.set(1, update);
                            update.addParent(this);
                            Z3Proof.hypModCount++;
                            this.markHypCacheDirty();
                            recomputeObsoleteLiterals();
                        }

                    }
                }

                // Remove obsolete resolution steps

                assert (subProofs.get(0).consequent instanceof OrFormula);
                assert (subProofs.get(1).consequent instanceof OrFormula);
                OrFormula obsoleteClause = Util.findObsoleteClause(
                        (OrFormula) subProofs.get(0).consequent,
                        (OrFormula) subProofs.get(1).consequent,
                        obsoleteLiterals);
                if (obsoleteClause != null) {
                    TransformedZ3Proof.numberOfRemovedObsoloteResolutionSteps++;
                    Formula literal = Util.findResolvingLiteral(
                            (OrFormula) subProofs.get(0).consequent,
                            (OrFormula) subProofs.get(1).consequent);

                    Collection<Formula> newObsoleteLiterals = obsoleteClause
                            .getDisjuncts();
                    if (!newObsoleteLiterals.remove(literal))
                        if (!newObsoleteLiterals.remove(Util
                                .invertLiteral(literal)))
                            assert (false); // One of the polarities must be
                                            // contained

                    Z3Proof nonObsoleteProof = null;
                    if (obsoleteClause.equals(subProofs.get(0).consequent)) {
                        nonObsoleteProof = subProofs.get(1);
                    } else {
                        assert (obsoleteClause
                                .equals(subProofs.get(1).consequent));
                        nonObsoleteProof = subProofs.get(0);
                    }
                    assert (nonObsoleteProof != null);
                    assert (nonObsoleteProof instanceof TransformedZ3Proof);
                    this.takeValuesFrom(nonObsoleteProof);
                    obsoleteLiterals = obsoleteLiterals
                            .addAllToCopy(newObsoleteLiterals);
                }
            }

            this.setHasBeenMadeLocal();

            if (!this.hasSingleLiteralConsequent())
                // For single literals, we still need to add an annotated node
                return;
        }

        if (this.hasSingleLiteralConsequent()) {
            // Add a new annotated node for this single-literal-consequent
            // node.
            AnnotatedProofNode annotatedNode = createNewAnnotatedNodeFromProofWithSingleLiteralConsequent(this);
            if (annotatedNode != null)
                TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                        annotatedNode);
            return;
        }

        // If we reach here, we are in case that was not foreseen.
        assert (false);
    }

    /**
     * (Re-)computes the set of obsolete literals as the union of obsolete
     * literals of the subproofs. Existing obsolete literals are overwritten and
     * will not be present any more, unless they also occur in a subproof.
     */
    private void recomputeObsoleteLiterals() {
        obsoleteLiterals = ImmutableSet.create(new HashSet<Formula>());
        for (Z3Proof subproof : subProofs) {
            assert (subproof instanceof TransformedZ3Proof);
            obsoleteLiterals = obsoleteLiterals
                    .addAllToCopy(((TransformedZ3Proof) subproof).obsoleteLiterals);
        }
    }

    private AnnotatedProofNode createNewAnnotatedNodeFromProofWithSingleLiteralConsequent(
            TransformedZ3Proof proof) {
        assert (proof.hasSingleLiteralConsequent());
        Formula literal = Util.getSingleLiteral(proof.consequent);

        if (literal.equals(PropositionalConstant.create(false)))
            // We do not need an AnnotatedNode for false.
            return null;

        Set<Integer> partitions = literal.getPartitionsFromSymbols();
        assert (partitions.size() > 0);
        partitions.remove(-1);
        if (partitions.size() > 1)
            // this is a bad literal. We ignore it. It will be
            // removed anyway
            return null;

        int partition;
        if (partitions.size() == 0)
            partition = 1; // put global stuff in partition 1 (arbitrary
                           // choice)
        else {
            assert (partitions.iterator().hasNext());
            assert (partitions.size() == 1);
            partition = partitions.iterator().next();
        }

        AnnotatedProofNode annotatedNode = new AnnotatedProofNode(partition,
                partition, proof, null, null, null);
        return annotatedNode;
    }

    private void handleSymmetry() {
        Z3Proof subproof = subProofs.get(0);
        Formula premiseLiteral = Util.getSingleLiteral(subproof.consequent);

        Set<Formula> newObsoleteLiterals = new HashSet<Formula>();
        AnnotatedProofNode annotatedNode = TransformedZ3Proof.annotatedNodesStack
                .peekFirst().getNodeWithConsequent(premiseLiteral,
                        subproof.getHypothesisFormulas(), newObsoleteLiterals);
        obsoleteLiterals = obsoleteLiterals.addAllToCopy(newObsoleteLiterals);
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
            TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                    new AnnotatedProofNode(annotatedNode.getPartition(),
                            annotatedNode.getPartition(), this, null, null,
                            null));
        } else {
            assert (numPremises == 3);
            TransformedZ3Proof newSymmetry1 = TransformedZ3Proof
                    .createSymmetryProof(annotatedNode.getPremise3());
            AnnotatedProofNode newPremise1 = new AnnotatedProofNode(
                    newSymmetry1);
            TransformedZ3Proof.annotatedNodesStack.peekFirst().add(newPremise1);
            TransformedZ3Proof newSymmetry2 = TransformedZ3Proof
                    .createSymmetryProof(annotatedNode.getPremise2());
            AnnotatedProofNode newPremise2 = new AnnotatedProofNode(
                    newSymmetry2);
            TransformedZ3Proof.annotatedNodesStack.peekFirst().add(newPremise2);
            TransformedZ3Proof newSymmetry3 = TransformedZ3Proof
                    .createSymmetryProof(annotatedNode.getPremise1());
            AnnotatedProofNode newPremise3 = new AnnotatedProofNode(
                    newSymmetry3);
            TransformedZ3Proof.annotatedNodesStack.peekFirst().add(newPremise3);

            TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                    new AnnotatedProofNode(annotatedNode.getRightPartition(),
                            annotatedNode.getLeftPartition(), this,
                            newPremise1, newPremise2, newPremise3));
        }

    }

    private void handleMonotonicity() {
        assert (subProofs.size() >= 1);

        Formula consequentLiteral = Util.getSingleLiteral(consequent);
        if (!(consequentLiteral instanceof EqualityFormula))
            assert (false);
        EqualityFormula consequentEq = (EqualityFormula) consequentLiteral;
        Term leftTerm = consequentEq.getTerms().get(0);
        Term rightTerm = consequentEq.getTerms().get(
                consequentEq.getTerms().size() - 1);

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

            Set<Formula> newObsoleteLiterals = new HashSet<Formula>();
            for (int count = 0; count < subProofs.size(); count++) {
                assert (subProofs.get(count) instanceof TransformedZ3Proof);
                Z3Proof subProof = subProofs.get(count);
                Set<Formula> currentNewObsoleteLiterals = new HashSet<Formula>();
                AnnotatedProofNode currentAnnotatedNode = TransformedZ3Proof.annotatedNodesStack
                        .peekFirst().getNodeWithConsequent(subProof.consequent,
                                subProof.getHypothesisFormulas(),
                                currentNewObsoleteLiterals);
                newObsoleteLiterals.addAll(currentNewObsoleteLiterals);
                if (currentAnnotatedNode.numPremises() == 3) {
                    List<TransformedZ3Proof> proofs = new ArrayList<TransformedZ3Proof>(
                            3);
                    proofs.add(currentAnnotatedNode.getPremise1());
                    proofs.add(currentAnnotatedNode.getPremise2());
                    proofs.add(currentAnnotatedNode.getPremise3());
                    TransformedZ3Proof newProof = TransformedZ3Proof
                            .createTransitivityProofForTransformedZ3Proofs(proofs);
                    this.subProofs.set(count, newProof);
                    newProof.addParent(this);
                    newProof.setHasBeenMadeLocal();

                    Z3Proof.hypModCount++;
                    this.markHypCacheDirty();
                    TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                            new AnnotatedProofNode(newProof));
                }
            }
            this.recomputeObsoleteLiterals();
            this.obsoleteLiterals = this.obsoleteLiterals
                    .addAllToCopy(newObsoleteLiterals);
            TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                    new AnnotatedProofNode(this));
            return;
        }

        List<DomainTerm> newLeftTerms = new ArrayList<DomainTerm>();
        List<DomainTerm> newRightTerms = new ArrayList<DomainTerm>();
        List<TransformedZ3Proof[]> proofs = new ArrayList<TransformedZ3Proof[]>();

        for (int count = 0; count < subProofs.size(); count++) {
            AnnotatedProofNode currentAnnotatedNode = TransformedZ3Proof.annotatedNodesStack
                    .peekFirst().getNodeWithConsequent(
                            subProofs.get(count).consequent,
                            subProofs.get(count).getHypothesisFormulas(),
                            new HashSet<Formula>());
            assert (currentAnnotatedNode != null);
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

        TransformedZ3Proof proof1 = null;
        TransformedZ3Proof proof2 = null;
        TransformedZ3Proof proof3 = null;

        if (consequentEq.getTerms().get(0) instanceof UninterpretedFunctionInstance) {
            UninterpretedFunction function = Util
                    .getUninterpretedFunctionOrPredicate(consequentLiteral);
            proof1 = TransformedZ3Proof.createMonotonicityProof(proofs1,
                    function);
            proof2 = TransformedZ3Proof.createMonotonicityProof(proofs2,
                    function);
            proof3 = TransformedZ3Proof.createMonotonicityProof(proofs3,
                    function);
        } else {
            Formula leftFormula = null;
            if (consequentEq.getTerms().get(0) instanceof FormulaTerm)
                leftFormula = ((FormulaTerm) consequentEq.getTerms().get(0))
                        .getFormula();
            else {
                assert (consequentEq.getTerms().get(0) instanceof PropositionalTerm);
                leftFormula = ((PropositionalTerm) consequentEq.getTerms().get(
                        0));
            }
            assert (leftFormula != null);

            Formula rightFormula = null;
            if (consequentEq.getTerms().get(1) instanceof FormulaTerm)
                rightFormula = ((FormulaTerm) consequentEq.getTerms().get(1))
                        .getFormula();
            else {
                assert (consequentEq.getTerms().get(1) instanceof PropositionalTerm);
                rightFormula = ((PropositionalTerm) consequentEq.getTerms()
                        .get(1));
            }
            assert (rightFormula != null);

            if (leftFormula instanceof UninterpretedPredicateInstance) {
                assert (rightFormula instanceof UninterpretedPredicateInstance);
                UninterpretedFunction function = Util
                        .getUninterpretedFunctionOrPredicate(consequentLiteral);
                proof1 = TransformedZ3Proof.createMonotonicityProof(proofs1,
                        function);
                proof2 = TransformedZ3Proof.createMonotonicityProof(proofs2,
                        function);
                proof3 = TransformedZ3Proof.createMonotonicityProof(proofs3,
                        function);

            } else {
                assert (leftFormula instanceof DomainEq);
                assert (rightFormula instanceof DomainEq);
                proof1 = TransformedZ3Proof
                        .createMonotonicityProofForEquality(proofs1);
                proof2 = TransformedZ3Proof
                        .createMonotonicityProofForEquality(proofs2);
                proof3 = TransformedZ3Proof
                        .createMonotonicityProofForEquality(proofs3);
            }
        }
        assert (proof1 != null);
        assert (proof2 != null);
        assert (proof3 != null);

        AnnotatedProofNode newPremise1 = new AnnotatedProofNode(proof1);
        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(newPremise1);
        AnnotatedProofNode newPremise2 = new AnnotatedProofNode(proof2);
        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(newPremise2);
        AnnotatedProofNode newPremise3 = new AnnotatedProofNode(proof3);
        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(newPremise3);

        // put things together, add new annotated node
        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                new AnnotatedProofNode(leftPartition, rightPartition, this,
                        newPremise1, newPremise2, newPremise3));
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
        if (newLeftTerm.equals(newRightTerm)) {
            result[1] = TransformedZ3Proof.createReflexivityProof(newLeftTerm);
        } else if (annotatedNode.numPremises() == 3) {
            assert (newProofNode != null);
            result[1] = newProofNode;
        } else {
            assert (annotatedNode.numPremises() == 0);
            if (leftTerm.equals(newLeftTerm)) {
                if (!rightTerm.equals(newRightTerm))
                    assert (false);
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
     * Converts a modus ponens node into something usable. Also, converts the
     * necessary parents into local (transformed) proofs.
     * 
     * @param z3Proof
     *            a modus ponens node
     * @return the conversion result
     */
    private static TransformedZ3Proof convertModusPonens(Z3Proof z3Proof) {

        assert (z3Proof.proofType.equals(SExpressionConstants.MODUS_PONENS));
        assert (z3Proof.getSubProofs().size() == 2);
        assert (z3Proof.hasSingleLiteralConsequent());
        Z3Proof child1 = z3Proof.getSubProofs().get(0);

        // Simple case of flipped equality or disequality
        if (Util.checkForFlippedEqualityOrDisequality(z3Proof.consequent,
                child1.consequent)) {
            TransformedZ3Proof transformedChild1 = TransformedZ3Proof
                    .convertToTransformedZ3Proof(child1);
            List<TransformedZ3Proof> subProofs = new ArrayList<TransformedZ3Proof>(
                    1);
            subProofs.add(transformedChild1);
            TransformedZ3Proof result = new TransformedZ3Proof(
                    SExpressionConstants.SYMMETRY, subProofs,
                    z3Proof.consequent);

            // assert (z3Proof.getHypotheses().size() == result.getHypotheses()
            // .size()); // DEBUG
            return result;
        }

        boolean chainOverEqualityAsPredicate = false;

        // Case of a transitivity chain
        if (Util.makeLiteralPositive(Util.getSingleLiteral(z3Proof.consequent)) instanceof DomainEq) {
            TransitivityChainBuilder chainBuilder = new TransitivityChainBuilder(
                    z3Proof);
            Set<Z3Proof> children = new HashSet<Z3Proof>();
            for (Z3Proof child : z3Proof.subProofs)
                Util.getModusPonensNonIffChilds(child, children);

            Set<TransformedZ3Proof> transformedChildren = new HashSet<TransformedZ3Proof>();
            for (Z3Proof child : children) {
                // Recursive call for child
                TransformedZ3Proof transformedChild = TransformedZ3Proof
                        .convertToTransformedZ3Proof(child);
                transformedChildren.add(transformedChild);
                chainBuilder.addProofNode(transformedChild);
            }

            List<TransformedZ3Proof> proofList = chainBuilder.getChain();
            if (proofList != null) {

                TransformedZ3Proof transProof = TransformedZ3Proof
                        .createTransitivityProofForTransformedZ3Proofs(proofList);

                assert (z3Proof.consequent.transformToConsequentsForm()
                        .equals(transProof.consequent
                                .transformToConsequentsForm()));

                // If we have three subproofs, we need to split them,
                // because conversion to local proof cannot deal with
                // three subproofs.
                // NOTE: This should (meanwhile) have been implemented in
                // createTransititivityProof directly!
                // Thus, the code following this assert is commented out.
                assert (transProof.subProofs.size() <= 2);
                // if (subProofs.size() == 3) {
                // assert (this.proofType == SExpressionConstants.TRANSITIVITY);
                // Z3Proof intermediate = Z3Proof
                // .createTransitivityProof(new ArrayList<Z3Proof>(
                // subProofs.subList(0, 2)));
                // Z3Proof rest = subProofs.get(2);
                // subProofs.clear();
                // subProofs.add(intermediate);
                // subProofs.add(rest);
                // }
                return transProof;
            } else {
                // Could not create a "normal" transitivity chain
                // Try viewing equality as a predicate instead, and
                // construct a chain to convert to resolution.
                chainOverEqualityAsPredicate = true;

            }
        }

        if (Util.makeLiteralPositive(Util.getSingleLiteral(z3Proof.consequent)) instanceof UninterpretedPredicateInstance
                || chainOverEqualityAsPredicate) {

            assert (Util
                    .makeLiteralPositive(Util
                            .getSingleLiteral(z3Proof.subProofs.get(0)
                                    .getConsequent())) instanceof UninterpretedPredicateInstance || chainOverEqualityAsPredicate);

            assert (!chainOverEqualityAsPredicate || Util
                    .makeLiteralPositive(Util
                            .getSingleLiteral(z3Proof.subProofs.get(0)
                                    .getConsequent())) instanceof EqualityFormula);

            boolean predicatePolarity = Util
                    .isAtom(Util.getSingleLiteral(z3Proof.subProofs.get(0)
                            .getConsequent()));

            assert (predicatePolarity || Util
                    .isNegativeLiteral(Util.getSingleLiteral(z3Proof.subProofs
                            .get(0).getConsequent())));

            // Collect relevant parents
            Set<Z3Proof> leafs = new HashSet<Z3Proof>();
            Set<Z3Proof> iffsComingFromDomainEq = new HashSet<Z3Proof>();
            assert (z3Proof.subProofs.size() == 2);
            for (Z3Proof child : z3Proof.subProofs) {
                Util.getModusPonensIffLeafs(child, leafs);
                if (!(Util.makeLiteralPositive(Util
                        .getSingleLiteral(child.consequent)) instanceof PropositionalEq))
                    continue;
                Util.getModusPonensIffChildsComingFromDomainEq(child,
                        iffsComingFromDomainEq);
            }

            Set<TransformedZ3Proof> relevantChildren = new HashSet<TransformedZ3Proof>();
            for (Z3Proof child : leafs) {
                TransformedZ3Proof transformedChild = TransformedZ3Proof
                        .convertToTransformedZ3Proof(child);
                relevantChildren.add(transformedChild);
            }
            for (Z3Proof child : iffsComingFromDomainEq) {
                TransformedZ3Proof transformedChild = TransformedZ3Proof
                        .convertToTransformedZ3Proof(child);
                relevantChildren.add(transformedChild);
            }

            // Build transitivity chain for the propositional equalities
            Term startTerm = FormulaTerm
                    .create(Util.makeLiteralPositive(Util
                            .getSingleLiteral(z3Proof.subProofs.get(0)
                                    .getConsequent())));
            Term endTerm = FormulaTerm.create(Util.makeLiteralPositive(Util
                    .getSingleLiteral(z3Proof.consequent)));
            TransitivityChainBuilder chainBuilder = new TransitivityChainBuilder(
                    startTerm, endTerm);
            for (TransformedZ3Proof child : relevantChildren) {
                chainBuilder.addProofNode(child);
            }

            TransformedZ3Proof resolutionChild = chainBuilder
                    .convertToResolutionChain(predicatePolarity);
            assert (resolutionChild != null);
            List<TransformedZ3Proof> subProofs = new ArrayList<TransformedZ3Proof>(
                    2);
            subProofs.add(TransformedZ3Proof
                    .convertToTransformedZ3Proof(child1));
            subProofs.add(resolutionChild);

            TransformedZ3Proof result = new TransformedZ3Proof(
                    SExpressionConstants.UNIT_RESOLUTION, subProofs,
                    z3Proof.consequent);

            assert (result.checkZ3ProofNode()); // DEBUG
            return result;
        }

        // If we reach here, this modus ponens node as an unforeseen structure
        // that we cannot handle.
        throw new RuntimeException("Unable to handle modus ponens node "
                + z3Proof.id);

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

        AnnotatedProofNode firstAnnotatedNode = TransformedZ3Proof.annotatedNodesStack
                .peekFirst().getNodeWithConsequent(subProofs.get(0).consequent,
                        subProofs.get(0).getHypothesisFormulas(),
                        new HashSet<Formula>());
        assert (firstAnnotatedNode != null);

        AnnotatedProofNode secondAnnotatedNode = TransformedZ3Proof.annotatedNodesStack
                .peekFirst().getNodeWithConsequent(subProofs.get(1).consequent,
                        subProofs.get(1).getHypothesisFormulas(),
                        new HashSet<Formula>());
        assert (secondAnnotatedNode != null);

        if (firstAnnotatedNode.numPremises() == 0
                && secondAnnotatedNode.numPremises() == 0) {
            if (firstAnnotatedNode.getPartition() == secondAnnotatedNode
                    .getPartition())
                handleTransitivityCase1();
            else
                handleTransitivityCase2(firstAnnotatedNode, secondAnnotatedNode);
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
     */
    private void handleTransitivityCase1() {
        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                new AnnotatedProofNode(this));
    }

    /**
     * Deals with the case that both equalities have annotated nodes with 0
     * premises, but from different partitions.
     * 
     */
    private void handleTransitivityCase2(
            AnnotatedProofNode firstAnnotatedProofNode,
            AnnotatedProofNode secondAnnotatedProofNode) {
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
        AnnotatedProofNode annotatedReflexivity = new AnnotatedProofNode(
                reflexivity);
        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                annotatedReflexivity);

        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                new AnnotatedProofNode(firstAnnotatedProofNode.getPartition(),
                        secondAnnotatedProofNode.getPartition(), this,
                        firstAnnotatedProofNode, annotatedReflexivity,
                        secondAnnotatedProofNode));
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
        newProofNode.setHasBeenMadeLocal();
        AnnotatedProofNode newAnnotatedNode = new AnnotatedProofNode(
                newProofNode);
        TransformedZ3Proof.annotatedNodesStack.peekFirst()
                .add(newAnnotatedNode);

        // assert (newProofNode.checkZ3ProofNode());
        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                new AnnotatedProofNode(firstAnnotatedNode.getLeftPartition(),
                        firstAnnotatedNode.getRightPartition(), this,
                        firstAnnotatedNode.getAnnotatedPremise1(),
                        firstAnnotatedNode.getAnnotatedPremise2(),
                        newAnnotatedNode));
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
        newProofNode.setHasBeenMadeLocal();
        AnnotatedProofNode newAnnotatedNode = new AnnotatedProofNode(
                newProofNode);
        TransformedZ3Proof.annotatedNodesStack.peekFirst()
                .add(newAnnotatedNode);

        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                new AnnotatedProofNode(firstAnnotatedNode.getPartition(),
                        secondAnnotatedNode.getRightPartition(), this,
                        newAnnotatedNode, secondAnnotatedNode
                                .getAnnotatedPremise2(), secondAnnotatedNode
                                .getAnnotatedPremise3()));

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
        newProofNode.setHasBeenMadeLocal();
        AnnotatedProofNode newAnnotatedNode = new AnnotatedProofNode(
                newProofNode);
        TransformedZ3Proof.annotatedNodesStack.peekFirst()
                .add(newAnnotatedNode);

        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                new AnnotatedProofNode(firstAnnotatedNode.getLeftPartition(),
                        secondAnnotatedNode.getPartition(), this,
                        firstAnnotatedNode.getAnnotatedPremise1(),
                        newAnnotatedNode, secondAnnotatedNode));

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
        newProofNode.setHasBeenMadeLocal();
        AnnotatedProofNode newAnnotatedNode = new AnnotatedProofNode(
                newProofNode);
        TransformedZ3Proof.annotatedNodesStack.peekFirst()
                .add(newAnnotatedNode);
        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                new AnnotatedProofNode(firstAnnotatedNode.getPartition(),
                        secondAnnotatedNode.getRightPartition(), this,
                        firstAnnotatedNode, newAnnotatedNode,
                        secondAnnotatedNode.getAnnotatedPremise3()));
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
        newProofNode1.setHasBeenMadeLocal();
        List<TransformedZ3Proof> newSubProofs2 = new ArrayList<TransformedZ3Proof>();
        newSubProofs2.add(firstAnnotatedNode.getPremise2());
        newSubProofs2.add(newProofNode1);
        newSubProofs2.add(secondAnnotatedNode.getPremise2());
        TransformedZ3Proof newProofNode2 = TransformedZ3Proof
                .createTransitivityProofForTransformedZ3Proofs(newSubProofs2);
        newProofNode2.setHasBeenMadeLocal();
        AnnotatedProofNode newAnnotatedNode1 = new AnnotatedProofNode(
                newProofNode1);
        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                newAnnotatedNode1);
        AnnotatedProofNode newAnnotatedNode2 = new AnnotatedProofNode(
                newProofNode2);
        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                newAnnotatedNode2);

        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                new AnnotatedProofNode(firstAnnotatedNode.getLeftPartition(),
                        secondAnnotatedNode.getRightPartition(), this,
                        firstAnnotatedNode.getAnnotatedPremise1(),
                        newAnnotatedNode2, secondAnnotatedNode
                                .getAnnotatedPremise3()));
    }

    /**
     * 
     * @return A list of all leafs of this proof.
     */
    @Deprecated
    public List<TransformedZ3Proof> getLeafs() {

        long operationId = DagOperationManager.startDAGOperation();
        List<TransformedZ3Proof> result = this.getLeafsRecursion(operationId);
        DagOperationManager.endDAGOperation(operationId);

        return result;
    }

    @Deprecated
    private List<TransformedZ3Proof> getLeafsRecursion(long operationId) {
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
     * Creates a symmetry proof for the given premise.
     * 
     * @param premise
     *            must have a single literal as a consequence
     * @return a symmetry proof for the given premise.
     */
    public static TransformedZ3Proof createSymmetryProof(
            TransformedZ3Proof premise) {
        Z3Proof z3Proof = Z3Proof.createSymmetryProof(premise);
        List<TransformedZ3Proof> newSubProofs = new ArrayList<TransformedZ3Proof>(
                3);
        for (Z3Proof subProof : z3Proof.subProofs) {
            assert (subProof instanceof TransformedZ3Proof);
            newSubProofs.add((TransformedZ3Proof) subProof);
        }
        TransformedZ3Proof result = new TransformedZ3Proof(z3Proof.proofType,
                newSubProofs, z3Proof.consequent);

        return result;
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

        // Reflexivity is axiomatically true. So it's safe to add
        // it at any time.
        if (TransformedZ3Proof.annotatedNodesStack.size() == 0)
            TransformedZ3Proof.annotatedNodesStack
                    .addFirst(new AnnotatedProofNodes());

        TransformedZ3Proof.annotatedNodesStack.peekFirst().add(
                new AnnotatedProofNode(result));
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

        Z3Proof z3Proof = Z3Proof.createTransitivityProof(subProofs);
        List<TransformedZ3Proof> newSubProofs = new ArrayList<TransformedZ3Proof>(
                2);

        for (Z3Proof subProof : z3Proof.subProofs) {
            assert (subProof instanceof TransformedZ3Proof);
            newSubProofs.add((TransformedZ3Proof) subProof);
        }
        return new TransformedZ3Proof(z3Proof.proofType, newSubProofs,
                z3Proof.consequent);
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
                UninterpretedFunctionInstance leftInstance = UninterpretedFunctionInstance
                        .create(function, leftParams);
                UninterpretedFunctionInstance rightInstance = UninterpretedFunctionInstance
                        .create(function, rightParams);
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
                UninterpretedPredicateInstance leftInstance = UninterpretedPredicateInstance
                        .create(function, leftParams);
                UninterpretedPredicateInstance rightInstance = UninterpretedPredicateInstance
                        .create(function, rightParams);
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
     * Creates a monotonicity proof with equality as the "function".
     * 
     * @param subProofs
     *            the equality proofs for the arguments
     * @return a monotonicity proof for the given parameters.
     */
    public static TransformedZ3Proof createMonotonicityProofForEquality(
            List<TransformedZ3Proof> subProofs) {

        if (subProofs.size() != 2)
            assert (false);
        assert (Util.getSingleLiteral(subProofs.get(0).consequent) instanceof DomainEq);
        assert (Util.getSingleLiteral(subProofs.get(1).consequent) instanceof DomainEq);

        List<DomainTerm> leftParams = new ArrayList<DomainTerm>(2);
        List<DomainTerm> rightParams = new ArrayList<DomainTerm>(2);

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
        assert (leftParams.size() == 2);
        assert (rightParams.size() == 2);

        DomainEq leftEq;
        DomainEq rightEq;
        try {
            leftEq = (DomainEq) EqualityFormula.create(leftParams, true);
            rightEq = (DomainEq) EqualityFormula.create(rightParams, true);
        } catch (IncomparableTermsException exc) {
            throw new RuntimeException("Incomparable terms!", exc);
        }

        List<PropositionalTerm> propTerms = new ArrayList<PropositionalTerm>(2);
        propTerms.add(FormulaTerm.create(leftEq));
        propTerms.add(FormulaTerm.create(rightEq));

        Formula consequent = PropositionalEq.create(propTerms, true);

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
     * 
     * @see at.iaik.suraq.smtlib.Z3Proof#isHypothesis()
     */
    @Override
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
            Set<Z3Proof> nodes = nodesOnPathToHypothesisFormula(hypothesis.consequent);
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
                newDisjuncts.remove(PropositionalConstant.create(false));
                newDisjuncts.add(negatedLiteral);
                node.consequent = (OrFormula.generate(newDisjuncts))
                        .transformToConsequentsForm();

                Z3Proof foundHypothesis = Util.findHypothesisInSubproofs(node,
                        hypothesis);
                if (foundHypothesis != null) {
                    Z3Proof other = node.subProofs.get(node.subProofs
                            .indexOf(foundHypothesis) == 0 ? 1 : 0);
                    assert (other instanceof TransformedZ3Proof);
                    TransformedZ3Proof otherChild = (TransformedZ3Proof) other;
                    node.takeValuesFrom(otherChild);
                    // Consequent must be overwritten with new value containing
                    // the hypothesis
                    node.consequent = (OrFormula.generate(newDisjuncts))
                            .transformToConsequentsForm();
                }
            }
        }
        return result;
    }

    /**
     * Transforms a proof with transitivity, monotonicity, resolution and
     * symmetry into a pure resolution proof
     * 
     * @param operationId
     *            TODO
     */
    public void toResolutionProof() {
        long operationId = DagOperationManager.startDAGOperation();
        this.toResolutionProofRecursion(operationId);
        DagOperationManager.endDAGOperation(operationId);
    }

    private void toResolutionProofRecursion(long operationId) {
        if (this.wasVisitedByDAGOperation(operationId))
            return;
        this.visitedByDAGOperation(operationId);

        if (this.proofType.equals(SExpressionConstants.LEMMA)) {
            assert (this.subProofs.size() == 1);
            assert (this.subProofs.get(0) instanceof TransformedZ3Proof);
            TransformedZ3Proof hypotheticalProof = (TransformedZ3Proof) this.subProofs
                    .get(0);
            assert (hypotheticalProof.consequent.equals((PropositionalConstant
                    .create(false)).transformToConsequentsForm()) || Util
                    .equalClauses(this.consequent, hypotheticalProof.consequent));

            if (hypotheticalProof.consequent.equals(PropositionalConstant
                    .create(false).transformToConsequentsForm())) {
                hypotheticalProof.toResolutionProofRecursion(operationId);
                hypotheticalProof.removeHypotheses();
            } else {
                assert (Util.equalClauses(this.consequent,
                        hypotheticalProof.consequent));
            }

            this.takeValuesFrom(hypotheticalProof);
            if (!(this.proofType.equals(SExpressionConstants.UNIT_RESOLUTION) || this.proofType
                    .equals(SExpressionConstants.ASSERTED)))
                assert (false);

            assert (!this.hypothesis);

            return;

        }

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
                axiomParts.add((NotFormula.create(subProof.consequent)));
            }

            axiomParts.add(this.consequent);
            OrFormula axiomFormula = (OrFormula.generate(axiomParts))
                    .transformToConsequentsForm();

            Z3Proof remainingAxiom = new TransformedZ3Proof(
                    SExpressionConstants.ASSERTED,
                    new ArrayList<TransformedZ3Proof>(), null,
                    axiomFormula.transformToConsequentsForm());

            for (int count = 0; count < this.subProofs.size() - 1; count++) {

                TransformedZ3Proof currentEquality = (TransformedZ3Proof) this.subProofs
                        .get(count);
                currentEquality.toResolutionProofRecursion(operationId);
                Formula literal = Util.getSingleLiteral(axiomParts.remove(0)
                        .transformToConsequentsForm());
                assert (Util.isLiteral(literal));

                remainingAxiom = new TransformedZ3Proof(
                        SExpressionConstants.UNIT_RESOLUTION, currentEquality,
                        remainingAxiom, literal.transformToConsequentsForm(),
                        (OrFormula.generate(axiomParts))
                                .transformToConsequentsForm());
            }

            TransformedZ3Proof currentEquality = (TransformedZ3Proof) this.subProofs
                    .get(this.subProofs.size() - 1);
            currentEquality.toResolutionProofRecursion(operationId);

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
                ((TransformedZ3Proof) child)
                        .toResolutionProofRecursion(operationId);
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
            z3SubProof.toResolutionProofRecursion(operationId);

            this.takeValuesFrom(z3SubProof);
            return;

        } else if (proofType.equals(SExpressionConstants.ASSERTED)
                || this.isHypothesis()) {
            assert (this.consequent instanceof OrFormula);

            // Too expensive?
            // assert (this.isLocal());
            assert (this.subProofs.size() == 0);
            return;

        } else {
            throw new RuntimeException("Encountered unexpected proof rule "
                    + proofType.toString()
                    + " while trying to rewrite z3 proof.");
        }
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

                children.add(Token.generate(child));
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

        long operationId = DagOperationManager.startDAGOperation();
        boolean result = this.isLocalRecursion(operationId);
        DagOperationManager.endDAGOperation(operationId);

        return result;
    }

    private boolean isLocalRecursion(long operationId) {
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
            List<PropositionalVariable> ctrlSignals,
            Map<PropositionalVariable, Formula> tseitinEncoding) {

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

            // Replace Tseitin variables
            Map<Token, Term> substitutionsMap = new HashMap<Token, Term>();
            for (PropositionalVariable tseitinVar : tseitinEncoding.keySet())
                substitutionsMap.put(Token.generate(tseitinVar.getVarName()),
                        FormulaTerm.create(tseitinEncoding.get(tseitinVar)));

            trees.put(signal, tree.substituteFormula(substitutionsMap,
                    new HashMap<SMTLibObject, SMTLibObject>()));
        }

        return trees;
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
                assert (literalPartitions.iterator().next() > 0);
                // This is resolution over a local literal.
                // ==> This node can be converted to ASSERTED
                // All parents should only resolve on locals as well.
                // TODO: Check parents!
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
                    return PropositionalIte.create(this.literal, rightResult,
                            leftResult);
                }
            } else if (!checkPresence(leftConsequent, this.literal)) {
                if (checkPresence(rightConsequent, this.literal)) {
                    // NOTE: Pudlak's "sel" works exactly opposite to "ite".
                    return PropositionalIte.create(this.literal, leftResult,
                            rightResult);
                }
            } else
                throw new RuntimeException("found invalid unit-resolution.");
        } else if (this.proofType.equals(SExpressionConstants.ASSERTED)) {

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

            return PropositionalConstant.create(isSet);

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

    /**
     * 
     * @return <code>true</code> if this is not a resolution node,
     *         <code>literal</code> is <code>null</code>, or if the exactly 2
     *         subproofs contain the resolving literal in opposite polarity.
     */
    private boolean checkLiteralOccurenceInSubProofs() {
        if (!this.proofType.equals(SExpressionConstants.UNIT_RESOLUTION))
            return true;

        if (literal == null)
            return true;

        if (this.subProofs.size() != 2)
            return false;

        assert (subProofs.get(0).consequent instanceof OrFormula);
        assert (subProofs.get(1).consequent instanceof OrFormula);

        OrFormula premise1 = (OrFormula) subProofs.get(0).consequent;
        OrFormula premise2 = (OrFormula) subProofs.get(0).consequent;

        Formula negatedLiteral = NotFormula.create(literal);

        int polarity = 0;
        for (Formula literalFromPremise1 : premise1.getDisjuncts()) {
            literalFromPremise1 = Util.getSingleLiteral(literalFromPremise1);
            if (literal.equals(literalFromPremise1)) {
                polarity = 1;
                break;
            }
            if (negatedLiteral.equals(literalFromPremise1)) {
                polarity = -1;
                break;
            }
        }
        if (polarity == 0)
            return false;
        for (Formula literalFromPremise2 : premise2.getDisjuncts()) {
            literalFromPremise2 = Util.getSingleLiteral(literalFromPremise2);
            assert (polarity != 0);
            if (polarity < 0) {
                if (literal.equals(literalFromPremise2))
                    return true;
            } else {
                assert (polarity > 0);
                if (negatedLiteral.equals(literalFromPremise2))
                    return true;
            }
        }
        return false;
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
                "Neither literal nor negated literal found! This should not happen!!");
    }

    /**
     * @return the <code>numberOfRemovedObsoloteResolutionSteps</code>
     */
    public static long getNumberOfRemovedObsoloteResolutionSteps() {
        return TransformedZ3Proof.numberOfRemovedObsoloteResolutionSteps;
    }

    /**
     * @return the <code>hasBeenMadeLocal</code>
     */
    public boolean isHasBeenMadeLocal() {
        return hasBeenMadeLocal;
    }

    /**
     * Sets the <code>hasBeenMadeLocalFlag</code> to <code>true</code>.
     */
    public void setHasBeenMadeLocal() {
        // Do a quick, sound, but non-complete check
        // At least, the direct parents must also have the flag set.
        for (Z3Proof child : subProofs) {
            assert (child instanceof TransformedZ3Proof);
            if (!(((TransformedZ3Proof) child).hasBeenMadeLocal))
                assert (false);
        }
        this.hasBeenMadeLocal = true;
    }
}