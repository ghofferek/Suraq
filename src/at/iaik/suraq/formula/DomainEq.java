/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

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

    /**
     * Returns a list (copy) of the terms compared by this formula.
     * 
     * @return a list of the terms compared by this formula.
     */
    public List<DomainTerm> getDomainTerms() {
        List<DomainTerm> terms = new ArrayList<DomainTerm>();
        for (Term term : this.terms)
            terms.add(((DomainTerm) term));
        return terms;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        List<DomainTerm> terms = new ArrayList<DomainTerm>();
        for (Term term : this.terms) {
            terms.add((DomainTerm) term.deepTermCopy());
        }
        return new DomainEq(terms, equal);
    }
}
