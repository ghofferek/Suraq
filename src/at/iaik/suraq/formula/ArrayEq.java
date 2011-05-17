/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

/**
 * A formula consisting of the equality of two array terms.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class ArrayEq extends Formula {

    /**
     * The terms to be compared.
     */
    private final ArrayTerm[] arrayTerms;

    /**
     * 
     * Constructs a new <code>TermEq</code>.
     * 
     * @param term1
     *            the first term of the equality.
     * @param term2
     *            the second term of the equality.
     */
    public ArrayEq(ArrayTerm arrayTerm1, ArrayTerm arrayTerm2) {
        arrayTerms = new ArrayTerm[2];
        arrayTerms[0] = arrayTerm1;
        arrayTerms[1] = arrayTerm2;
    }
}
