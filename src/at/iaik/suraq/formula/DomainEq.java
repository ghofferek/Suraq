/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Collection;

/**
 * A formula consisting of the equality of domain terms.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class DomainEq extends EqualityFormula {

    /**
     * 
     * Constructs a new <code>TermEq</code>.
     * 
     * @param terms
     *            the terms of the (in)equality.
     * @param equal
     *            <code>true</code> if an equality should be constructed,
     *            <code>false</code> for an inequality.
     * 
     */
    public DomainEq(Collection<DomainTerm> domainTerms, boolean equal) {
        super(domainTerms, equal);
    }
}
