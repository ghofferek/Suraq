/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Collection;

/**
 * A formula consisting of the (in)equality of propositional terms.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalEq extends EqualityFormula {
    /**
     * 
     * Constructs a new <code>PropositionalEq</code>.
     * 
     * @param terms
     *            the terms of the (in)equality.
     * @param equal
     *            <code>true</code> if an equality should be constructed,
     *            <code>false</code> for an inequality.
     * 
     */
    public PropositionalEq(Collection<PropositionalTerm> propTerms, boolean equal) {
        super(propTerms, equal);
    }
}
