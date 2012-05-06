/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import at.iaik.suraq.formula.Formula;
import at.iaik.suraq.formula.NotFormula;
import at.iaik.suraq.formula.OrFormula;
import at.iaik.suraq.formula.ProofFormula;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 *         This class represents a resolution-style proof, which is the first
 *         intermediate step in the series of proof transformations: z3 proof
 *         --> non-local resolution proof --> local resolution proof -->
 *         reordered local resolution proof. I.e., z3 proof rules will be
 *         converted into axioms and resolution over them. Splitting of axioms
 *         in order to localize the proof will be the next step.
 * 
 */
public class NonLocalResolutionProof {

    /**
     * The two antecedents of the proof. These can be <code>null</code>, e.g.,
     * if the consequent was already asserted (i.e., for leaves of the proof).
     */
    private NonLocalResolutionProof[] subProofs = new NonLocalResolutionProof[2];

    /**
     * The "literal" on which resolution is applied. This could e.g. be an
     * equality of the form (a=b), or (f(a)=c). It could also be a propositional
     * variable, or an (uninterpreted) predicate instance. <code>literal</code>
     * will be <code>null</code> for leaves of the proof. In non-leave nodes,
     * <code>literal</code> should store the positive (=non-negated) form of the
     * resolution literal. I.e., <code>literal</code> should not be of type
     * <code>NotFormula</code>.
     */
    private Formula literal;

    /**
     * This formula is the consequent of this proof. It should either be an
     * <code>OrFormula</code> or the constant formula <code>false</code>.
     */
    private Formula consequent;

    public NonLocalResolutionProof(NonLocalResolutionProof antecedent1,
            NonLocalResolutionProof antecedent2, Formula literal,
            Formula consequent) {
        subProofs[0] = antecedent1;
        subProofs[1] = antecedent2;
        this.literal = literal.deepFormulaCopy();
        this.consequent = consequent;

        // TODO: Check if this is a valid resolution step. I.e., the consequent
        // does not contain the literal any more, but the antecedents both
        // contain it in different phase. Also, check the structure of the
        // formulas
    }

    public NonLocalResolutionProof(ProofFormula z3Proof) {

        // Go through all possible cases of z3 proof rules

        Token proofType = z3Proof.getProofType();

        if (proofType.equals(SExpressionConstants.ASSERTED)) {
            // This is a leave of the proof tree.
            subProofs[0] = null;
            subProofs[1] = null;
            consequent = z3Proof.getProofFormula(); // TODO Check the structure
                                                    // of this formula
            literal = null;
            return;
        } else if (proofType.equals(SExpressionConstants.AND_ELIM)) {
            // Treat this as a leave.
            // Relies on the assumption that and-elim is only used for things
            // that have been asserted, and not on things are are proven
            // separately.
            subProofs[0] = null;
            subProofs[1] = null;
            consequent = z3Proof.getProofFormula(); // TODO Check the structure
                                                    // of this formula
            literal = null;
            return;
        } else if (proofType.equals(SExpressionConstants.NOT_OR_ELIM)) {
            // Treat this as a leave.
            // Relies on the assumption that not-or-elim is only used for things
            // that have been asserted, and not on things are are proven
            // separately.
            subProofs[0] = null;
            subProofs[1] = null;
            consequent = z3Proof.getProofFormula(); // TODO Check the structure
                                                    // of this formula
            literal = null;
            return;
        } else if (proofType.equals(SExpressionConstants.REFLEXIVITY)) {
            // Treat this as a leave, since it is axiomatically true.
            subProofs[0] = null;
            subProofs[1] = null;
            consequent = z3Proof.getProofFormula(); // TODO Check the structure
                                                    // of this formula
            literal = null;
            return;
        } else if (proofType.equals(SExpressionConstants.SYMMETRY)) {
            // Ignore symmetry. a=b and b=a should be treated as the
            // same object by later steps anyway.
            // NOTE (GH): Not sure if this is actually a correct assumption.
            List<ProofFormula> z3SubProofs = z3Proof.getSubProofs();
            if (z3SubProofs.size() != 1)
                throw new RuntimeException(
                        "Symmetry proof with not exactly one child. This should not happen!");
            ProofFormula z3SubProof = z3SubProofs.get(0);
            NonLocalResolutionProof tmp = new NonLocalResolutionProof(
                    z3SubProof);
            this.consequent = tmp.consequent;
            this.subProofs = tmp.subProofs;
            this.literal = tmp.literal;
            return;
        } else if (proofType.equals(SExpressionConstants.TRANSITIVITY)) {
            List<ProofFormula> z3SubProofs = z3Proof.getSubProofs();
            if (z3SubProofs.size() != 2)
                throw new RuntimeException(
                        "Transitivity proof with not exactly two children. This should not happen!");
            ProofFormula z3SubProof1 = z3SubProofs.get(0);
            ProofFormula z3SubProof2 = z3SubProofs.get(1);
            List<Formula> axiomParts = new ArrayList<Formula>();
            axiomParts.add(new NotFormula(z3SubProof1.getProofFormula()));
            axiomParts.add(new NotFormula(z3SubProof2.getProofFormula()));
            axiomParts.add(z3Proof.getProofFormula());
            OrFormula axiomFormula = new OrFormula(axiomParts);

            List<Formula> intermediateResultParts = new ArrayList<Formula>();
            intermediateResultParts.add(new NotFormula(z3SubProof2
                    .getProofFormula()));
            intermediateResultParts.add(z3Proof.getProofFormula());
            OrFormula intermediateResultFormula = new OrFormula(
                    intermediateResultParts);

            // Recursion for subproofs
            NonLocalResolutionProof subProof1 = new NonLocalResolutionProof(
                    z3SubProof1);
            NonLocalResolutionProof subProof2 = new NonLocalResolutionProof(
                    z3SubProof2);

            // Putting things together
            NonLocalResolutionProof axiom = new NonLocalResolutionProof(null,
                    null, null, axiomFormula);
            NonLocalResolutionProof firstResolutionStep = new NonLocalResolutionProof(
                    subProof1, axiom, z3SubProof1.getProofFormula(),
                    intermediateResultFormula);
            this.subProofs[0] = subProof2;
            this.subProofs[1] = firstResolutionStep;
            this.literal = z3SubProof2.getProofFormula();
            return;
        } else if (proofType.equals(SExpressionConstants.MONOTONICITY)) {
            List<ProofFormula> z3SubProofs = z3Proof.getSubProofs();
            if (z3SubProofs.size() < 1)
                throw new RuntimeException(
                        "Monotonicity proof with less than one child. This should not happen!");

            List<Formula> axiomParts = new ArrayList<Formula>();
            for (ProofFormula z3SubProof : z3Proof.getSubProofs())
                axiomParts.add(new NotFormula(z3SubProof.getProofFormula()));
            axiomParts.add(z3Proof.getProofFormula());
            OrFormula axiomFormula = new OrFormula(axiomParts);

            NonLocalResolutionProof remainingAxiom = new NonLocalResolutionProof(
                    null, null, null, axiomFormula);
            for (int count = 0; count < z3SubProofs.size() - 1; count++) {
                NonLocalResolutionProof currentEquality = new NonLocalResolutionProof(
                        z3SubProofs.get(count));
                axiomParts.remove(0);
                remainingAxiom = new NonLocalResolutionProof(currentEquality,
                        remainingAxiom, z3SubProofs.get(count)
                                .getProofFormula(), new OrFormula(axiomParts));
            }
            this.subProofs[0] = new NonLocalResolutionProof(
                    z3SubProofs.get(z3SubProofs.size() - 1));
            this.subProofs[1] = remainingAxiom;
            this.literal = z3SubProofs.get(z3SubProofs.size() - 1)
                    .getProofFormula();
            this.consequent = z3Proof.getProofFormula();
            return;

        } else if (proofType.equals(SExpressionConstants.UNIT_RESOLUTION)) {
            List<ProofFormula> z3SubProofs = z3Proof.getSubProofs();
            if (z3SubProofs.size() < 2)
                throw new RuntimeException(
                        "Unit-Resolution proof with less than two child. This should not happen!");
            NonLocalResolutionProof nonUnitAntecedent = new NonLocalResolutionProof(
                    z3SubProofs.get(0));
            if (!(nonUnitAntecedent.consequent instanceof OrFormula))
                throw new RuntimeException(
                        "Antecedent of Unit-Resolution proof is not an OrFormula. This should not happen.");
            OrFormula remainingNonUnitFormula = (OrFormula) nonUnitAntecedent.consequent;

            for (int count = 1; count < z3SubProofs.size() - 1; count++) {
                Collection<Formula> newDisjuncts = remainingNonUnitFormula
                        .getDisjuncts();
                newDisjuncts.remove(z3SubProofs.get(count).getProofFormula());
                remainingNonUnitFormula = new OrFormula(newDisjuncts);
                nonUnitAntecedent = new NonLocalResolutionProof(
                        new NonLocalResolutionProof(z3SubProofs.get(count)),
                        nonUnitAntecedent, z3SubProofs.get(count)
                                .getProofFormula(), remainingNonUnitFormula);
            }
            // TODO last step (= initialize "this").
        }
        // TODO hypothesis? lemma?

        // TODO add other relevant cases, if any
        else {
            throw new RuntimeException("Encountered unexpected proof rule "
                    + proofType.toString()
                    + " while trying to rewrite z3 proof.");
        }

    }
}
