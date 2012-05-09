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
import at.iaik.suraq.proof.AnnotatedProofNode;
import at.iaik.suraq.proof.AnnotatedProofNodes;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.Term;

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
    private boolean isAxiom = false; // FIXME Do we really need this?

    /**
     * Storage for annotated nodes used during proof conversion.
     */
    private static AnnotatedProofNodes annotatedNodes = new AnnotatedProofNodes();

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
            Formula literal = ((OrFormula) (this.proofFormula)).getDisjuncts()
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
            Formula premiseLiteral = ((OrFormula) (subproof.proofFormula))
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

    }

    /**
     * Deals with transforming a transitivity node to a local proof.
     */
    private void handleTransitivity() {
        assert (subProofs.size() == 2);

        AnnotatedProofNode firstAnnotatedNode = TransformedZ3Proof.annotatedNodes
                .getNodeWithConsequent(subProofs.get(0).proofFormula);
        assert (firstAnnotatedNode != null);

        AnnotatedProofNode secondAnnotatedNode = TransformedZ3Proof.annotatedNodes
                .getNodeWithConsequent(subProofs.get(1).proofFormula);
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
                handleTransitivityCase3();
            else
                handleTransitivityCase5();
        } else if (firstAnnotatedNode.numPremises() == 0
                && secondAnnotatedNode.numPremises() == 3) {
            if (firstAnnotatedNode.getLeftPartition() == secondAnnotatedNode
                    .getLeftPartition())
                handleTransitivityCase4();
            else
                handleTransitivityCase6();
        } else if (firstAnnotatedNode.numPremises() == 3
                && secondAnnotatedNode.numPremises() == 3) {
            handleTransitivityCase7();
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
        assert (subProofs.get(0).proofFormula instanceof EqualityFormula);
        EqualityFormula formula = (EqualityFormula) subProofs.get(0).proofFormula;
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
     * 
     */
    private void handleTransitivityCase3() {
        // TODO Auto-generated method stub

    }

    /**
     * 
     */
    private void handleTransitivityCase4() {
        // TODO Auto-generated method stub

    }

    /**
     * 
     */
    private void handleTransitivityCase5() {
        // TODO Auto-generated method stub

    }

    /**
     * 
     */
    private void handleTransitivityCase6() {
        // TODO Auto-generated method stub

    }

    /**
     * 
     */
    private void handleTransitivityCase7() {
        // TODO Auto-generated method stub

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
        Formula literal = ((OrFormula) (premise.proofFormula)).getDisjuncts()
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
        result.isAxiom = true;
        return result;
    }
}