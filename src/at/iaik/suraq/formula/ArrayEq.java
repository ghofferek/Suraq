/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

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

    /**
     * @see at.iaik.suraq.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        List<ArrayTerm> terms = new ArrayList<ArrayTerm>();
        for (Term term : this.terms) {
            terms.add((ArrayTerm) term.deepTermCopy());
        }
        return new ArrayEq(terms, equal);
    }
}
