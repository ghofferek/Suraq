/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.proof.AnnotatedProofNode;
import at.iaik.suraq.proof.AnnotatedProofNodes;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.smtlib.TransformedZ3Proof;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.FormulaTerm;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalEq;
import at.iaik.suraq.smtlib.formula.PropositionalTerm;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.util.graph.Graph;

/**
 * 
 * Helper class to build a chain of transitivity to proof a particular target
 * equality.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TransitivityChainBuilder {

    /**
     * The first term of the target equality.
     */
    private final Term targetStartTerm;

    /**
     * The last term of the target equality.
     */
    private final Term targetEndTerm;

    /**
     * Graph of equalities.
     */
    private final Graph<Term, Z3Proof> graph = new Graph<Term, Z3Proof>(true);

    /**
     * 
     * Constructs a new <code>TransitivityChainBuilder</code>.
     * 
     * @param target
     *            the target to prove.
     */
    public TransitivityChainBuilder(Z3Proof target) {

        assert (Util.isLiteral(target.getConsequent()));
        Formula targetLiteral = Util.getSingleLiteral(target.getConsequent());
        targetLiteral = Util.makeLiteralPositive(targetLiteral);
        if (!(targetLiteral instanceof EqualityFormula))
            assert (false);
        EqualityFormula eq = (EqualityFormula) targetLiteral;
        assert (eq.getTerms().size() == 2);
        targetStartTerm = eq.getTerms().get(0);
        targetEndTerm = eq.getTerms().get(1);
    }

    public TransitivityChainBuilder(Term startTerm, Term endTerm) {
        this.targetStartTerm = startTerm;
        this.targetEndTerm = endTerm;
    }

    /**
     * Adds a new node that may be used to build the transitivity chain. If the
     * consequent of the node is not of type <code>EqualityFormula</code> (with
     * 2 terms), the node will be ignored.
     * 
     * @param node
     */
    public void addProofNode(TransformedZ3Proof node) {
        assert (Util.isLiteral(node.getConsequent()));
        Formula literal = Util.getSingleLiteral(node.getConsequent());
        literal = Util.makeLiteralPositive(literal);
        if (!(literal instanceof EqualityFormula)) {
            System.out
                    .println("INFO: Ignoring a node added to a chain builder.");
            return;
        }

        EqualityFormula newEq = (EqualityFormula) literal;
        if (newEq.getTerms().size() != 2) {
            System.out
                    .println("INFO: Ignoring a node added to a chain builder.");
            return;
        }

        Term term1 = newEq.getTerms().get(0);
        Term term2 = newEq.getTerms().get(1);

        graph.addEdge(term1, term2, node);
        Z3Proof symmetry = Z3Proof.createSymmetryProof(node);
        graph.addEdge(term2, term1, symmetry);
    }

    /**
     * 
     * @return a list of proofs that forms the desired transitivity chain, or
     *         <code>null</code> if no path has been found in the graph.
     * 
     */
    public List<TransformedZ3Proof> getChain() {
        List<Z3Proof> chain = graph.findPath(targetStartTerm, targetEndTerm);
        List<TransformedZ3Proof> transformedChain = new ArrayList<TransformedZ3Proof>(
                chain.size());
        for (Z3Proof proof : chain) {
            TransformedZ3Proof transformedProof = TransformedZ3Proof
                    .convertToTransformedZ3Proof(proof);
            assert (proof.getConsequent().transformToConsequentsForm()
                    .equals(transformedProof.getConsequent()
                            .transformToConsequentsForm()));
            transformedChain.add(transformedProof);
        }
        return transformedChain;
    }

    /**
     * Converts the transitivity chain into a resolution chain. This is used for
     * modus ponens nodes with uninterpreted predicates.
     * 
     * @param predicatePolarity
     *            the polarity of the predicate in the first child of the modus
     *            ponens node.
     * @return a proof with for a clause with two literals. The first is the
     *         inverse of the first modus ponens child. The second is the
     *         consequent of the modus ponens node.
     */
    public TransformedZ3Proof convertToResolutionChain(boolean predicatePolarity) {

        assert (targetStartTerm instanceof FormulaTerm);
        assert (targetEndTerm instanceof FormulaTerm);

        boolean reversePolarity = false;
        List<Z3Proof> tmpChain = graph.findPath(targetStartTerm, targetEndTerm);

        if (tmpChain == null) {
            reversePolarity = true;
            FormulaTerm reverseStartTerm = new FormulaTerm(new NotFormula(
                    ((FormulaTerm) targetStartTerm).getFormula()));
            FormulaTerm reverseEndTerm = new FormulaTerm(new NotFormula(
                    ((FormulaTerm) targetEndTerm).getFormula()));
            tmpChain = graph.findPath(reverseStartTerm, reverseEndTerm);
            if (tmpChain == null)
                assert (false);
        }

        List<TransformedZ3Proof> chain = new ArrayList<TransformedZ3Proof>(
                tmpChain.size());
        for (Z3Proof proof : tmpChain) {
            TransformedZ3Proof transformedProof = TransformedZ3Proof
                    .convertToTransformedZ3Proof(proof);
            assert (Util.isLiteral(transformedProof.getConsequent()));
            if (Util.isBadLiteral(Util.getSingleLiteral(transformedProof
                    .getConsequent()))) {
                AnnotatedProofNodes annotatedNodes = transformedProof
                        .toLocalProof();
                AnnotatedProofNode annotatedNode = annotatedNodes
                        .getNodeWithConsequent(transformedProof.getConsequent());
                assert (annotatedNode != null);
                assert (annotatedNode.numPremises() == 3);
                chain.add(annotatedNode.getPremise1());
                chain.add(annotatedNode.getPremise2());
                chain.add(annotatedNode.getPremise3());
            } else
                chain.add(transformedProof);
        }

        TransformedZ3Proof intermediate = null;

        for (TransformedZ3Proof current : chain) {
            assert (Util.getSingleLiteral(current.getConsequent()) instanceof PropositionalEq);
            PropositionalEq propEq = (PropositionalEq) Util
                    .getSingleLiteral(current.getConsequent());
            PropositionalTerm term1 = (PropositionalTerm) propEq.getTerms()
                    .get(0);
            PropositionalTerm term2 = (PropositionalTerm) propEq.getTerms()
                    .get(1);

            List<Formula> disjuncts = new ArrayList<Formula>(3);
            disjuncts.add(predicatePolarity ^ reversePolarity ? new NotFormula(
                    term1) : term1);
            disjuncts.add(predicatePolarity ^ reversePolarity ? term2
                    : new NotFormula(term2));

            if (current.getProofType().equals(SExpressionConstants.SYMMETRY)) {
                assert (current.getSubProofs().size() == 1);
                assert (current.getSubProofs().get(0) instanceof TransformedZ3Proof);
                current = (TransformedZ3Proof) current.getSubProofs().get(0);
            }

            if (current.getProofType().equals(SExpressionConstants.ASSERTED)) {
                current = new TransformedZ3Proof(SExpressionConstants.ASSERTED,
                        new ArrayList<TransformedZ3Proof>(0), new OrFormula(
                                disjuncts),
                        current.getAssertPartitionOfThisNode(), false);
                assert (current.checkZ3ProofNode()); // DEBUG
            } else {
                assert (current.getSubProofs().size() == 1 || current
                        .getSubProofs().size() == 2);

                if (current.getSubProofs().size() == 1) {

                    if (!(Util.getSingleLiteral(current.getSubProofs().get(0)
                            .getConsequent()) instanceof DomainEq))
                        assert (false);
                    disjuncts.add(new NotFormula(current.getSubProofs().get(0)
                            .getConsequent()));
                    TransformedZ3Proof axiom = new TransformedZ3Proof(
                            SExpressionConstants.ASSERTED,
                            new ArrayList<TransformedZ3Proof>(0),
                            new OrFormula(disjuncts),
                            current.getAssertPartitionOfThisNode(), true);
                    List<TransformedZ3Proof> subProofs = new ArrayList<TransformedZ3Proof>(
                            2);
                    assert (current.getSubProofs().get(0) instanceof TransformedZ3Proof);
                    subProofs.add((TransformedZ3Proof) current.getSubProofs()
                            .get(0));
                    subProofs.add(axiom);
                    current = new TransformedZ3Proof(
                            SExpressionConstants.UNIT_RESOLUTION, subProofs,
                            new OrFormula(disjuncts.subList(0, 2)));
                    assert (current.checkZ3ProofNode()); // DEBUG

                } else {
                    assert (current.getSubProofs().size() == 2);
                    assert (Util.getSingleLiteral(current.getSubProofs().get(0)
                            .getConsequent()) instanceof DomainEq);
                    assert (Util.getSingleLiteral(current.getSubProofs().get(1)
                            .getConsequent()) instanceof DomainEq);
                    disjuncts.add(new NotFormula(current.getSubProofs().get(1)
                            .getConsequent()));
                    disjuncts.add(new NotFormula(current.getSubProofs().get(0)
                            .getConsequent()));
                    TransformedZ3Proof axiom = new TransformedZ3Proof(
                            SExpressionConstants.ASSERTED,
                            new ArrayList<TransformedZ3Proof>(0),
                            new OrFormula(disjuncts),
                            current.getAssertPartitionOfThisNode(), true);
                    List<TransformedZ3Proof> currentSubProofs = new ArrayList<TransformedZ3Proof>();
                    for (Z3Proof proof : current.getSubProofs()) {
                        assert (proof instanceof TransformedZ3Proof);
                        currentSubProofs.add((TransformedZ3Proof) proof);
                    }
                    List<TransformedZ3Proof> subProofs = new ArrayList<TransformedZ3Proof>(
                            2);
                    subProofs.add(currentSubProofs.get(0));
                    subProofs.add(axiom);
                    current = new TransformedZ3Proof(
                            SExpressionConstants.UNIT_RESOLUTION, subProofs,
                            new OrFormula(disjuncts.subList(0, 3)));
                    assert (current.checkZ3ProofNode()); // DEBUG
                    subProofs = new ArrayList<TransformedZ3Proof>(2);
                    subProofs.add(currentSubProofs.get(1));
                    subProofs.add(current);
                    current = new TransformedZ3Proof(
                            SExpressionConstants.UNIT_RESOLUTION, subProofs,
                            new OrFormula(disjuncts.subList(0, 2)));
                    assert (current.checkZ3ProofNode()); // DEBUG
                }
            }
            if (intermediate == null)
                intermediate = current;
            else {
                List<TransformedZ3Proof> subProofs = new ArrayList<TransformedZ3Proof>(
                        2);
                subProofs.add(intermediate);
                subProofs.add(current);
                List<Formula> intermediateDisjuncts = new ArrayList<Formula>(2);
                intermediateDisjuncts.add(((OrFormula) intermediate
                        .getConsequent()).getDisjuncts().get(0));
                intermediateDisjuncts.add(((OrFormula) current.getConsequent())
                        .getDisjuncts().get(1));
                intermediate = new TransformedZ3Proof(
                        SExpressionConstants.UNIT_RESOLUTION, subProofs,
                        new OrFormula(intermediateDisjuncts));
                assert (intermediate.checkZ3ProofNode()); // DEBUG
            }
        }
        return intermediate;
    }
}
