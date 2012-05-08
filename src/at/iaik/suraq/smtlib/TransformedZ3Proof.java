/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.proof.AnnotatedProofNode;
import at.iaik.suraq.proof.AnnotatedProofNodes;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.OrFormula;

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
    private boolean isAxiom = false;

    public TransformedZ3Proof(Z3Proof z3proof) {

        // FIXME
        super(null, null, null);
    }

    public TransformedZ3Proof(Token proofType,
            List<TransformedZ3Proof> subProofs, Formula proofFormula) {
        super(proofType, subProofs, proofFormula);
        // TODO Auto-generated constructor stub
    }

    /**
     * Transforms the proof into a local resolution proof (in place).
     */
    public void toLocalResolutionProof() {
        this.computeParents(); // FIXME this is most probably a redundant call.
                               // getLeafs() should also compute the parents.
        List<TransformedZ3Proof> queue = this.getLeafs();
        AnnotatedProofNodes annotatedNodes = new AnnotatedProofNodes();
        while (!queue.isEmpty()) {
            TransformedZ3Proof currentNode = queue.remove(0);
            if (currentNode.hasSingleLiteralConsequent()) {
                Formula literal = ((OrFormula) (currentNode.proofFormula))
                        .getDisjuncts().iterator().next();

                // -------------------------------------------------------------
                if (currentNode.proofType.equals(SExpressionConstants.ASSERTED)) {
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
                            partition, partition, literal, null, null, null);
                    annotatedNodes.add(annotatedNode);
                }

                // -------------------------------------------------------------
                if (currentNode.proofType.equals(SExpressionConstants.SYMMETRY)) {
                    AnnotatedProofNode annotatedNode = annotatedNodes
                            .getNodeWithConsequent(literal);
                    if (annotatedNode == null)
                        throw new RuntimeException(
                                "No annotated proof node found when there should be one.");
                    int numPremises = annotatedNode.numPremises();
                    if (numPremises != 1 && numPremises != 3)
                        throw new RuntimeException(
                                "Unexpected number of premises for annotated symmetry node: "
                                        + (new Integer(numPremises)).toString());
                    if (numPremises == 1) {
                        assert (currentNode.subProofs.size() == 1);
                        TransformedZ3Proof premise = (TransformedZ3Proof) currentNode.subProofs
                                .get(0);
                        assert (premise.hasSingleLiteralConsequent());
                        Formula premiseFormula = premise.getProofFormula();
                        annotatedNodes.add(new AnnotatedProofNode(annotatedNode
                                .getPartition(), annotatedNode.getPartition(),
                                literal, premiseFormula, null, null));
                    }
                }
            }
        }
    }

    /**
     * @return <code>true</code> if the consequent of this node has only a
     *         single literal.
     */
    private boolean hasSingleLiteralConsequent() {
        OrFormula consequent = (OrFormula) this.proofFormula;
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
}