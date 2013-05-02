/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.IncomparableTermsException;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.util.FormulaCache;

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
    private PropositionalEq(Collection<? extends PropositionalTerm> propTerms,
            boolean equal) {
        super(propTerms, equal);
    }

    public static PropositionalEq create(
            Collection<? extends PropositionalTerm> propTerms, boolean equal) {
        return (PropositionalEq) FormulaCache.equalityFormula
                .put(new PropositionalEq(propTerms, equal));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return this; // experimental
        /*
         * List<PropositionalTerm> terms = new ArrayList<PropositionalTerm>();
         * for (Term term : this.terms) { terms.add((PropositionalTerm)
         * term.deepTermCopy()); } return new PropositionalEq(terms, equal);
         */
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.List,
     *      java.util.Map)
     */
    @Override
    public PropositionalVariable tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding, int partition) {
        List<ImpliesFormula> conjuncts = new ArrayList<ImpliesFormula>(2);

        // A circle is enough:
        // A = B = C
        // A => B ^ B => C ^ C => A

        PropositionalTerm term1 = (PropositionalTerm) terms.get(0);
        for (int i = 1; i < terms.size(); i++) {
            PropositionalTerm termi = (PropositionalTerm) terms.get(i);
            conjuncts.add(ImpliesFormula.create(term1, termi));
        }

        PropositionalTerm termlast = (PropositionalTerm) terms
                .get(terms.size() - 1);
        conjuncts.add(ImpliesFormula.create(termlast, term1));

        if (terms.size() != 2)
            System.err
                    .println("PropositionalVariable:tseitinEncode: Was not implemented correctly, but is now.");

        // old version:
        /*
         * assert (terms.size() == 2); PropositionalTerm term1 =
         * (PropositionalTerm) terms.get(0); PropositionalTerm term2 =
         * (PropositionalTerm) terms.get(1); // TODO: split larger equalities
         * 
         * assert (clauses != null); assert (encoding != null);
         * 
         * conjuncts.add(ImpliesFormula.create(term1, term2));
         * conjuncts.add(ImpliesFormula.create(term2, term1));
         */

        return (AndFormula.generate(conjuncts).tseitinEncode(clauses, encoding,
                partition));
    }

    @Override
    public Formula replaceEquivalences(Formula topLeveFormula,
            Map<EqualityFormula, String> replacements,
            Set<Token> noDependenceVars) {
        ArrayList<Term> terms2 = new ArrayList<Term>();
        for (int i = 0; i < terms.size(); i++) {
            PropositionalTerm term = (PropositionalTerm) terms.get(i);
            Formula newterm = term.replaceEquivalences(topLeveFormula,
                    replacements, noDependenceVars);
            terms2.add((PropositionalTerm) newterm);
        }
        try {
            return EqualityFormula.create(terms2, equal);
        } catch (IncomparableTermsException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }
}
