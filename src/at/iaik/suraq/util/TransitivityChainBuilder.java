/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.List;

import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
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
}
