package at.iaik.suraq.smtlib;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;

public class ResolutionZ3Proof extends Z3Proof {

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
     * Creates a new <code>ResolutionZ3Proof</code>.
     * 
     * @param proofType
     *            type of the proof.
     * @param subProofs
     *            the subproofs.
     * @param consequent
     *            the consequent.
     * 
     */
    public ResolutionZ3Proof(Token proofType,
            List<ResolutionZ3Proof> subProofs, Formula consequent) {

        super(proofType, subProofs, consequent.transformToConsequentsForm()
                .deepFormulaCopy());
    }

    /**
     * Creates a new <code>ResolutionZ3Proof</code>.
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
    public ResolutionZ3Proof(Token proofType,
            List<ResolutionZ3Proof> subProofs, Formula literal,
            Formula consequent) {

        super(proofType, subProofs, consequent.transformToConsequentsForm());

        this.literal = literal;
    }

    /**
     * Creates a new <code>ResolutionZ3Proof</code>.
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
    public ResolutionZ3Proof(Token proofType, ResolutionZ3Proof subProof1,
            ResolutionZ3Proof subProof2, Formula literal, Formula consequent) {

        super(proofType, subProof1, subProof2, consequent
                .transformToConsequentsForm().deepFormulaCopy());

        this.literal = literal.deepFormulaCopy();
    }

    public ResolutionZ3Proof(TransformedZ3Proof z3Proof) {

        // Go through all possible cases of z3 proof rules

        Token proofType = z3Proof.getProofType();

        if (proofType.equals(SExpressionConstants.TRANSITIVITY)) {
            List<Z3Proof> z3SubProofs = z3Proof.getSubProofs();
            if (z3SubProofs.size() != 2)
                throw new RuntimeException(
                        "Transitivity proof with not exactly two children. This should not happen!");

            Z3Proof z3SubProof1 = z3SubProofs.get(0);
            Z3Proof z3SubProof2 = z3SubProofs.get(1);
            List<Formula> axiomParts = new ArrayList<Formula>();
            axiomParts.add((new NotFormula(z3SubProof1.getConsequent()))
                    .transformToConsequentsForm());
            axiomParts.add((new NotFormula(z3SubProof2.getConsequent()))
                    .transformToConsequentsForm());
            axiomParts.add(z3Proof.getConsequent());
            OrFormula axiomFormula = new OrFormula(axiomParts);

            List<Formula> intermediateResultParts = new ArrayList<Formula>();
            intermediateResultParts.add((new NotFormula(z3SubProof2
                    .getConsequent())).transformToConsequentsForm());
            intermediateResultParts.add(z3Proof.getConsequent());
            OrFormula intermediateResultFormula = new OrFormula(
                    intermediateResultParts);

            // Recursion for subproofs
            ResolutionZ3Proof subProof1 = new ResolutionZ3Proof(
                    (TransformedZ3Proof) z3SubProof1);
            ResolutionZ3Proof subProof2 = new ResolutionZ3Proof(
                    (TransformedZ3Proof) z3SubProof2);

            // Putting things together
            ResolutionZ3Proof axiom = new ResolutionZ3Proof(
                    SExpressionConstants.ASSERTED,
                    new ArrayList<ResolutionZ3Proof>(), null,
                    axiomFormula.transformToConsequentsForm());

            ResolutionZ3Proof firstResolutionStep = new ResolutionZ3Proof(
                    SExpressionConstants.UNIT_RESOLUTION, subProof1, axiom,
                    z3SubProof1.getConsequent().transformToConsequentsForm(),
                    intermediateResultFormula.transformToConsequentsForm());

            this.subProofs.add(subProof2);
            this.subProofs.add(firstResolutionStep);
            this.literal = z3SubProof2.getConsequent();
            this.consequent = z3Proof.getConsequent();
            this.proofType = SExpressionConstants.UNIT_RESOLUTION;

            return;

        } else if (proofType.equals(SExpressionConstants.MONOTONICITY)) {

            List<Z3Proof> z3SubProofs = z3Proof.getSubProofs();
            if (z3SubProofs.size() < 1)
                throw new RuntimeException(
                        "Monotonicity proof with less than one child. This should not happen!");

            List<Formula> axiomParts = new ArrayList<Formula>();
            for (Z3Proof z3SubProof : z3Proof.getSubProofs())
                axiomParts.add((new NotFormula(z3SubProof.getConsequent()))
                        .transformToConsequentsForm());

            axiomParts.add(z3Proof.getConsequent());
            OrFormula axiomFormula = new OrFormula(axiomParts);

            ResolutionZ3Proof remainingAxiom = new ResolutionZ3Proof(
                    SExpressionConstants.ASSERTED,
                    new ArrayList<ResolutionZ3Proof>(), null,
                    axiomFormula.transformToConsequentsForm());

            for (int count = 0; count < z3SubProofs.size() - 1; count++) {
                ResolutionZ3Proof currentEquality = new ResolutionZ3Proof(
                        (TransformedZ3Proof) z3SubProofs.get(count));
                axiomParts.remove(0);
                remainingAxiom = new ResolutionZ3Proof(
                        SExpressionConstants.UNIT_RESOLUTION, currentEquality,
                        remainingAxiom, z3SubProofs.get(count).getConsequent()
                                .transformToConsequentsForm(), (new OrFormula(
                                axiomParts)).transformToConsequentsForm());
            }
            this.subProofs
                    .add(new ResolutionZ3Proof((TransformedZ3Proof) z3SubProofs
                            .get(z3SubProofs.size() - 1)));
            this.subProofs.add(remainingAxiom);
            this.literal = z3SubProofs.get(z3SubProofs.size() - 1)
                    .getConsequent().transformToConsequentsForm();
            this.consequent = z3Proof.getConsequent();
            this.proofType = SExpressionConstants.UNIT_RESOLUTION;
            return;

        } else if (proofType.equals(SExpressionConstants.UNIT_RESOLUTION)) {
            this.consequent = z3Proof.consequent;

            for (Z3Proof subProof : z3Proof.subProofs)
                this.subProofs.add(new ResolutionZ3Proof(
                        (TransformedZ3Proof) subProof));

            this.literal = z3Proof.getLiteral();
            this.proofType = SExpressionConstants.UNIT_RESOLUTION;

        } else if (proofType.equals(SExpressionConstants.SYMMETRY)) {
            // Ignore symmetry. a=b and b=a should be treated as the
            // same object by later steps anyway.
            // NOTE (GH): Not sure if this is actually a correct assumption.
            List<Z3Proof> z3SubProofs = z3Proof.getSubProofs();
            if (z3SubProofs.size() != 1)
                throw new RuntimeException(
                        "Symmetry proof with not exactly one child. This should not happen!");

            TransformedZ3Proof z3SubProof = (TransformedZ3Proof) z3SubProofs
                    .get(0);

            ResolutionZ3Proof tmp = new ResolutionZ3Proof(z3SubProof);
            this.consequent = tmp.consequent;
            this.subProofs = tmp.subProofs;
            this.literal = tmp.literal;
            this.proofType = tmp.proofType;
            return;

        } else if (proofType.equals(SExpressionConstants.ASSERTED)) {
            this.consequent = z3Proof.consequent;
            this.proofType = SExpressionConstants.ASSERTED;

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

        if (this.subProofs.size() == 2) {
            if (this.literal != null)
                children.add(new Token(this.proofType
                        + "{"
                        + this.literal.toString().replaceAll("\n", "")
                                .replaceAll("\\s{2,}", " ") + "}"));
            else
                throw new RuntimeException("resolution always need a literal");
        } else
            children.add(this.proofType);

        for (Z3Proof subProof : this.subProofs)
            children.add(subProof.toSmtlibV2());

        children.add(this.consequent.toSmtlibV2());
        return new SExpression(children);
    }

}
