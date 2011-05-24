/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Collection;

/**
 * A formula consisting of the (in)equality of array terms.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayEq extends EqualityFormula {

    /**
     * 
     * Constructs a new <code>ArrayEq</code>.
     * 
     * @param terms
     *            the terms of the (in)equality.
     * @param equal
     *            <code>true</code> if an equality should be constructed,
     *            <code>false</code> for an inequality.
     * 
     */
    public ArrayEq(Collection<ArrayTerm> arrayTerms, boolean equal) {
        super(arrayTerms, equal);
    }
}
