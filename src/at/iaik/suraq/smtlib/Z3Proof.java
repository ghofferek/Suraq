/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;

/**
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
public class Z3Proof implements SMTLibObject {

    /**
     * The proof type.
     */
    private Token proofType;

    /**
     * The list of sub proofs.
     */
    private List<Z3Proof> subProofs;

    /**
     * the formula which is proven
     */
    private Formula proofFormula;

    /**
     * 
     * Constructs a new <code>Z3Proof</code>.
     * 
     * @param proofType
     *            the type of the proof
     * @param subProofs
     *            the list of all subproofs
     * @param proofFormula
     *            the formula which has to be proved
     */
    public Z3Proof(Token proofType, List<Z3Proof> subProofs,
            Formula proofFormula) {

        this.proofType = proofType;
        assert (subProofs != null);
        this.subProofs = subProofs;
        this.proofFormula = proofFormula;
    }

    /**
     * Creates a new <code>Z3Proof</code> which is of the same type as
     * <code>this</code> object and has the given subProofs and proofFormula.
     * 
     * @param subProofs
     *            List of sub-proofs
     * @param proofFormula
     *            the proofFormula
     * @return a new <code>Z3Proof</code> with the same type as
     *         <code>this</code>.
     */
    protected Z3Proof create(List<Z3Proof> subProofs, Formula proofFormula) {

        List<Z3Proof> newSubProofs = new ArrayList<Z3Proof>();

        for (Z3Proof subProof : subProofs) {
            newSubProofs.add(subProof);
        }

        Z3Proof instance = new Z3Proof(new Token(this.proofType), newSubProofs,
                proofFormula);

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
     * @return the <code>proofFormula</code>
     */
    public Formula getProofFormula() {
        return this.proofFormula;
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

        children.add(this.proofFormula.toSmtlibV2());
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
    public Set<Integer> getAssertPartition() {
        Set<Integer> partitions = proofFormula.getAssertPartition();

        for (Z3Proof proof : subProofs)
            partitions.addAll(proof.getAssertPartition());

        return partitions;
    }
}
