/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

/**
 * A formula consisting of the (in)equality of propositional terms.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalEq extends EqualityFormula {
    /**
     * 
     */
    private static final long serialVersionUID = 3110446371682510102L;

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
    public PropositionalEq(Collection<? extends PropositionalTerm> propTerms,
            boolean equal) {
        super(propTerms, equal);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        List<PropositionalTerm> terms = new ArrayList<PropositionalTerm>();
        for (Term term : this.terms) {
            terms.add((PropositionalTerm) term.deepTermCopy());
        }
        return new PropositionalEq(terms, equal);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.List,
     *      java.util.Map)
     */
    @Override
    public PropositionalVariable tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding) {

        assert (terms.size() == 2);
        PropositionalTerm term1 = (PropositionalTerm) terms.get(0);
        PropositionalTerm term2 = (PropositionalTerm) terms.get(1);
        // TODO: split larger equalities

        assert (clauses != null);
        assert (encoding != null);

        List<ImpliesFormula> conjuncts = new ArrayList<ImpliesFormula>(2);
        conjuncts.add(new ImpliesFormula(term1, term2));
        conjuncts.add(new ImpliesFormula(term2, term1));

        return (new AndFormula(conjuncts).tseitinEncode(clauses, encoding));
    }
}
