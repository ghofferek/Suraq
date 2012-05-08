/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.proof;

import at.iaik.suraq.smtlib.formula.Formula;

/**
 * 
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class AnnotatedProofNode {

    private final int leftPartition;

    private final int rightPartition;

    private final Formula consequent;

    private final Formula premise1;

    private final Formula premise2;

    private final Formula premise3;

    private final int hash;

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
            Formula consequent, Formula premise1, Formula premise2,
            Formula premise3) {
        super();
        this.leftPartition = leftPartition;
        this.rightPartition = rightPartition;
        this.consequent = consequent.deepFormulaCopy();

        assert (premise1 != null || (premise2 == null && premise3 == null));
        assert (premise2 != null || premise3 == null);

        this.premise1 = premise1 != null ? premise1.deepFormulaCopy() : null;
        this.premise2 = premise2 != null ? premise2.deepFormulaCopy() : null;
        this.premise3 = premise3 != null ? premise3.deepFormulaCopy() : null;

        this.hash = premise1.hashCode() ^ premise2.hashCode()
                ^ premise3.hashCode() ^ consequent.hashCode()
                ^ (new Integer(leftPartition)).toString().hashCode()
                ^ (new Integer(rightPartition)).toString().hashCode();
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
        if (!this.consequent.equals(other.consequent))
            return false;
        if (!(this.premise1 != null ? this.premise1.equals(other.premise1)
                : other.premise1 == null))
            return false;
        if (!(this.premise2 != null ? this.premise2.equals(other.premise2)
                : other.premise2 == null))
            return false;
        if (!(this.premise3 != null ? this.premise3.equals(other.premise3)
                : other.premise3 == null))
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
     * @return the <code>premise1</code> (copy)
     */
    public Formula getPremise1() {
        return premise1 == null ? null : premise1.deepFormulaCopy();
    }

    /**
     * @return the <code>premise2</code> (copy)
     */
    public Formula getPremise2() {
        return premise2 == null ? null : premise2.deepFormulaCopy();
    }

    /**
     * @return the <code>premise3</code> (copy)
     */
    public Formula getPremise3() {
        return premise3 == null ? null : premise3.deepFormulaCopy();
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

}
