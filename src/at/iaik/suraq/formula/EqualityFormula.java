/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class EqualityFormula implements Formula {
    /**
     * The terms to be compared.
     */
    protected final List<? extends Term> terms;

    /**
     * <code>true</code> for an equality, <code>false</code> for an inequality.
     */
    protected final boolean equal;

    protected EqualityFormula(Collection<? extends Term> terms, boolean equal) {
        this.equal = equal;
        ArrayList<Term> termList = new ArrayList<Term>();
        for (Term term : terms)
            termList.add(term);
        this.terms = termList;
    }

}
