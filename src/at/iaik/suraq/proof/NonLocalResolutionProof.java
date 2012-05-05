/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.proof;

import at.iaik.suraq.formula.Formula;
import at.iaik.suraq.formula.ProofFormula;
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
     * The two antecedents of the proof
     */
    private NonLocalResolutionProof[] subProofs = new NonLocalResolutionProof[2];

    /**
     * The "literal" on which resolution is applied. This could e.g. be an
     * equality of the form (a=b), or (f(a)=c). It could also be a propositional
     * variable, or an (uninterpreted) predicate instance.
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

        // TODO finish implementation

        this.consequent = z3Proof.getProofFormula();
    }

}
