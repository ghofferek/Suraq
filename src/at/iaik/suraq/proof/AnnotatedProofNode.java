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
     * Constructs a new <code>AnnotatedProofNode</code>.
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

}
