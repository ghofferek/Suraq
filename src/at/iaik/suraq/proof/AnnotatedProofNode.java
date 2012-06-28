/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.util.HashSet;
import java.util.Set;

import at.iaik.suraq.smtlib.TransformedZ3Proof;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.util.Util;

/**
 * 
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class AnnotatedProofNode {

    private final int leftPartition;

    private final int rightPartition;

    private final TransformedZ3Proof consequent;

    private final TransformedZ3Proof premise1;

    private final TransformedZ3Proof premise2;

    private final TransformedZ3Proof premise3;

    private final AnnotatedProofNode annotatedPremise1;

    private final AnnotatedProofNode annotatedPremise2;

    private final AnnotatedProofNode annotatedPremise3;

    private final int hash;

    private final Set<Formula> hypotheses;

    /**
     * Constructs a new <code>AnnotatedProofNode</code>. If one premise is
     * <code>null</code>, all subsequent premises must be <code>null</code> too.
     * 
     * @param leftPartition
     * @param rightPartition
     * @param consequent
     * @param premise1
     * @param premise2
     * @param premise3
     */
    public AnnotatedProofNode(int leftPartition, int rightPartition,
            TransformedZ3Proof consequent, AnnotatedProofNode premise1,
            AnnotatedProofNode premise2, AnnotatedProofNode premise3) {
        super();
        this.leftPartition = leftPartition;
        this.rightPartition = rightPartition;
        this.consequent = consequent;

        assert ((premise1 == null && premise2 == null && premise3 == null) || (premise1 != null
                && premise2 != null && premise3 != null));

        this.annotatedPremise1 = premise1;
        this.annotatedPremise2 = premise2;
        this.annotatedPremise3 = premise3;

        this.premise1 = premise1 == null ? null : premise1.consequent;
        this.premise2 = premise2 == null ? null : premise2.consequent;
        this.premise3 = premise3 == null ? null : premise3.consequent;

        if (numPremises() > 0) {

            assert (this.premise1 != null);
            assert (this.premise2 != null);
            assert (this.premise3 != null);

            hypotheses = new HashSet<Formula>();
            hypotheses.addAll(premise1.hypotheses);
            hypotheses.addAll(premise2.hypotheses);
            hypotheses.addAll(premise3.hypotheses);

            assert (Util.isLiteral(Util.getSingleLiteral(this.premise1
                    .getConsequent())));
            assert (Util.isLiteral(Util.getSingleLiteral(this.premise2
                    .getConsequent())));
            assert (Util.isLiteral(Util.getSingleLiteral(this.premise3
                    .getConsequent())));

            Formula[] premises = {
                    Util.getSingleLiteral(this.premise1.getConsequent()),
                    Util.getSingleLiteral(this.premise2.getConsequent()),
                    Util.getSingleLiteral(this.premise3.getConsequent()) };

            int numDisequalities = 0;
            for (Formula premise : premises) {
                if (Util.isNegativeLiteral(premise))
                    numDisequalities++;
            }
            assert (numDisequalities <= 1);

            Object[] part1 = ((EqualityFormula) Util.makeLiteralPositive(Util
                    .getSingleLiteral((this.premise1.getConsequent()))))
                    .getTerms().toArray();
            Object[] part2 = ((EqualityFormula) Util.makeLiteralPositive(Util
                    .getSingleLiteral((this.premise2.getConsequent()))))
                    .getTerms().toArray();
            Object[] part3 = ((EqualityFormula) Util.makeLiteralPositive(Util
                    .getSingleLiteral((this.premise3.getConsequent()))))
                    .getTerms().toArray();
            Object[] consequentTerms = ((EqualityFormula) Util
                    .makeLiteralPositive(Util.getSingleLiteral((this.consequent
                            .getConsequent())))).getTerms().toArray();

            if (!consequentTerms[0].equals(part1[0]))
                assert (false);
            assert (consequentTerms[1].equals(part3[1]));
            assert (part1[1].equals(part2[0]));
            assert (part2[1].equals(part3[0]));

            Set<Integer> premise1Partitions = this.premise1.getConsequent()
                    .getPartitionsFromSymbols();
            Set<Integer> premise2Partitions = this.premise2.getConsequent()
                    .getPartitionsFromSymbols();
            Set<Integer> premise3Partitions = this.premise3.getConsequent()
                    .getPartitionsFromSymbols();
            Set<Integer> consequentPartitions = this.consequent.getConsequent()
                    .getPartitionsFromSymbols();

            assert (premise1Partitions.size() == 1 || (premise1Partitions
                    .size() == 2 && premise1Partitions.contains(-1)));
            assert (premise1Partitions.contains(this.leftPartition) || (premise1Partitions
                    .size() == 1 && premise1Partitions.contains(-1)));
            assert (premise2Partitions.size() == 1 && premise2Partitions
                    .contains(-1));
            assert (premise3Partitions.size() == 1 || (premise3Partitions
                    .size() == 2 && premise3Partitions.contains(-1)));
            assert (premise3Partitions.contains(this.rightPartition) || (premise3Partitions
                    .size() == 1 && premise3Partitions.contains(-1)));
            assert (consequentPartitions.size() <= 3);
            assert (consequentPartitions.contains(leftPartition) || consequentPartitions
                    .contains(-1));
            assert (consequentPartitions.contains(rightPartition) || consequentPartitions
                    .contains(-1));
        } else {
            hypotheses = consequent.getHypothesisFormulas();
        }

        this.hash = (premise1 == null ? 0 : premise1.hashCode())
                ^ (premise2 == null ? 0 : premise2.hashCode())
                ^ (premise3 == null ? 0 : premise3.hashCode())
                ^ consequent.hashCode()
                ^ (new Integer(leftPartition)).toString().hashCode()
                ^ (new Integer(rightPartition)).toString().hashCode()
                ^ hypotheses.hashCode();
    }

    /**
     * Constructs a new <code>AnnotatedProofNode</code>.
     * 
     * @param transformedZ3Proof
     */
    public AnnotatedProofNode(TransformedZ3Proof transformedZ3Proof) {
        this(Util.getSinglePartitionOfProof(transformedZ3Proof), Util
                .getSinglePartitionOfProof(transformedZ3Proof),
                transformedZ3Proof, null, null, null);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return this.hash;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof AnnotatedProofNode))
            return false;
        AnnotatedProofNode other = (AnnotatedProofNode) obj;
        if (this.leftPartition != other.leftPartition)
            return false;
        if (this.rightPartition != other.rightPartition)
            return false;
        if (this.consequent != other.consequent)
            return false;
        if (this.premise1 != other.premise1)
            return false;
        if (this.premise2 != other.premise2)
            return false;
        if (this.premise3 != other.premise3)
            return false;
        return true;
    }

    /**
     * @param consequent
     *            the consequent to compare
     * @return <code>true</code> if the given consequent equals the one of this
     *         node
     */
    public boolean hasConsequent(Formula consequent) {
        return this.consequent.getConsequent().transformToConsequentsForm()
                .equals(consequent.transformToConsequentsForm());
    }

    /**
     * @param consequent
     *            the consequent to compare
     * @return <code>true</code> if the given consequent equals the one of this
     *         node
     */
    public boolean hasConsequent(Z3Proof consequent) {
        return this.consequent.equals(consequent);
    }

    /**
     * Returns the partition, if the left and the right partition are equal.
     * Throws a <code>RuntimeException</code> if they are different.
     * 
     * @return the partition of this node (left==right)
     */
    public int getPartition() {
        if (leftPartition != rightPartition)
            throw new RuntimeException(
                    "Left and right partitions are not equal!");

        return leftPartition;
    }

    /**
     * @return the <code>leftPartition</code>
     */
    public int getLeftPartition() {
        return leftPartition;
    }

    /**
     * @return the <code>rightPartition</code>
     */
    public int getRightPartition() {
        return rightPartition;
    }

    /**
     * @return the <code>consequent</code>
     */
    public TransformedZ3Proof getConsequent() {
        return consequent;
    }

    /**
     * @return the <code>premise1</code>
     */
    public TransformedZ3Proof getPremise1() {
        return premise1;
    }

    /**
     * @return the <code>premise2</code>
     */
    public TransformedZ3Proof getPremise2() {
        return premise2;
    }

    /**
     * @return the <code>premise3</code>
     */
    public TransformedZ3Proof getPremise3() {
        return premise3;
    }

    /**
     * Returns the number of (non-<code>null</code>) premises. Relies on the
     * fact that if one premise is <code>null</code>, all subsequent premises
     * must be <code>null</code> too.
     * 
     * @return the number of non-<code>null</code> premises.
     */
    public int numPremises() {
        if (premise1 == null)
            return 0;
        else if (premise2 == null)
            return 1;
        else if (premise3 == null)
            return 2;
        else
            return 3;
    }

    /**
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuffer buffer = new StringBuffer();

        buffer.append("Partitions: ");
        buffer.append(leftPartition);
        buffer.append(", ");
        buffer.append(rightPartition);
        buffer.append("\n");

        buffer.append("Premise 1: ");
        buffer.append(premise1 == null ? "null" : premise1.getConsequent()
                .toString().replaceAll("\\s{2,}", " ").replace("\n", ""));
        buffer.append("\n");

        buffer.append("Premise 2: ");
        buffer.append(premise2 == null ? "null" : premise2.getConsequent()
                .toString().replaceAll("\\s{2,}", " ").replace("\n", ""));
        buffer.append("\n");

        buffer.append("Premise 3: ");
        buffer.append(premise3 == null ? "null" : premise3.getConsequent()
                .toString().replaceAll("\\s{2,}", " ").replace("\n", ""));
        buffer.append("\n");

        buffer.append("Consequent: ");
        buffer.append(consequent == null ? "null" : consequent.getConsequent()
                .toString().replaceAll("\\s{2,}", " ").replace("\n", ""));
        buffer.append("\n");
        return buffer.toString();
    }

    /**
     * @return the <code>hypotheses</code> (copy)
     */
    public Set<Formula> getHypotheses() {
        return new HashSet<Formula>(hypotheses);
    }

    /**
     * @return the <code>annotatedPremise1</code>
     */
    public AnnotatedProofNode getAnnotatedPremise1() {
        return annotatedPremise1;
    }

    /**
     * @return the <code>annotatedPremise2</code>
     */
    public AnnotatedProofNode getAnnotatedPremise2() {
        return annotatedPremise2;
    }

    /**
     * @return the <code>annotatedPremise3</code>
     */
    public AnnotatedProofNode getAnnotatedPremise3() {
        return annotatedPremise3;
    }

}
