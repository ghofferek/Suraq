/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
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
    public void addProofNode(Z3Proof node) {
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
    public List<Z3Proof> getChain() {
        return graph.findPath(targetStartTerm, targetEndTerm);
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
    public Z3Proof convertToResolutionChain(boolean predicatePolarity) {

        List<Z3Proof> chain = graph.findPath(targetStartTerm, targetEndTerm);
        Z3Proof intermediate = null;

        for (Z3Proof current : chain) {
            assert (Util.getSingleLiteral(current.getConsequent()) instanceof PropositionalEq);
            PropositionalEq propEq = (PropositionalEq) Util
                    .getSingleLiteral(current.getConsequent());
            PropositionalTerm term1 = (PropositionalTerm) propEq.getTerms()
                    .get(0);
            PropositionalTerm term2 = (PropositionalTerm) propEq.getTerms()
                    .get(1);

            List<Formula> disjuncts = new ArrayList<Formula>(3);
            disjuncts.add(predicatePolarity ? new NotFormula(term1) : term1);
            disjuncts.add(predicatePolarity ? term2 : new NotFormula(term2));

            if (current.getProofType().equals(SExpressionConstants.ASSERTED)) {
                current = new Z3Proof(SExpressionConstants.ASSERTED,
                        new ArrayList<Z3Proof>(0), new OrFormula(disjuncts),
                        current.getAssertPartitionOfThisNode(), false);
                assert (current.checkZ3ProofNode()); // DEBUG
            } else {
                assert (current.getSubProofs().size() == 1);
                assert (Util.getSingleLiteral(current.getSubProofs().get(0)
                        .getConsequent()) instanceof DomainEq);
                disjuncts.add(new NotFormula(current.getSubProofs().get(0)
                        .getConsequent()));
                Z3Proof axiom = new Z3Proof(SExpressionConstants.ASSERTED,
                        new ArrayList<Z3Proof>(0), new OrFormula(disjuncts),
                        current.getAssertPartitionOfThisNode(), true);
                List<Z3Proof> subProofs = new ArrayList<Z3Proof>(2);
                subProofs.add(current.getSubProofs().get(0));
                subProofs.add(axiom);
                current = new Z3Proof(SExpressionConstants.UNIT_RESOLUTION,
                        subProofs, new OrFormula(disjuncts.subList(0, 2)));
                assert (current.checkZ3ProofNode()); // DEBUG
            }
            if (intermediate == null)
                intermediate = current;
            else {
                List<Z3Proof> subProofs = new ArrayList<Z3Proof>(2);
                subProofs.add(intermediate);
                subProofs.add(current);
                List<Formula> intermediateDisjuncts = new ArrayList<Formula>(2);
                intermediateDisjuncts.add(((OrFormula) intermediate
                        .getConsequent()).getDisjuncts().get(0));
                intermediateDisjuncts.add(((OrFormula) current.getConsequent())
                        .getDisjuncts().get(1));
                intermediate = new Z3Proof(
                        SExpressionConstants.UNIT_RESOLUTION, subProofs,
                        new OrFormula(intermediateDisjuncts));
                assert (intermediate.checkZ3ProofNode()); // DEBUG
            }
        }
        return intermediate;
    }
}
