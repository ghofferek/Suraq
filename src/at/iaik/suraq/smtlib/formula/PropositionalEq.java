/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
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
            Map<PropositionalVariable, Formula> encoding,
            Map<Formula, PropositionalVariable> done, int partition) {
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
                done, partition));
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

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getLiterals(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getLiterals(Set<Formula> result, Set<Formula> done) {
        for (Term term : terms) {
            assert (term instanceof PropositionalTerm);
            ((PropositionalTerm) term).getLiterals(result, done);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#numAigNodes(java.util.Set)
     */
    @Override
    public int numAigNodes(Set<Formula> done) {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toAig(TreeMap, java.util.Map)
     */
    @Override
    public int toAig(TreeMap<Integer, Integer[]> aigNodes,
            Map<Formula, Integer> done) {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.EqualityFormula#computeParents(java.util.Map,
     *      java.util.Set)
     */
    @Override
    public void computeParents(Map<Formula, Set<Formula>> parents,
            Set<Formula> done) {
        for (Term term : terms) {
            assert (term instanceof PropositionalTerm);
            PropositionalTerm propTerm = (PropositionalTerm) term;
            Set<Formula> childsParents = parents.get(propTerm);
            if (childsParents == null) {
                childsParents = new TreeSet<Formula>();
                parents.put(propTerm, childsParents);
            }
            assert (childsParents != null);
            childsParents.add(this);
            propTerm.computeParents(parents, done);
        }
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.EqualityFormula#dependsOnlyOn(java.util.Set)
     */
    @Override
    public boolean dependsOnlyOn(Set<Formula> formulaSet) {
        Set<Formula> propTerms = new HashSet<Formula>(terms.size() * 2);
        for (Term term : terms) {
            assert (term instanceof PropositionalTerm);
            propTerms.add((PropositionalTerm) term);
        }
        boolean result = formulaSet.containsAll(propTerms);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getTerms(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getTerms(Set<Term> result, Set<Formula> done) {
        if (done.contains(this))
            return;

        for (Term term : terms) {
            assert (term instanceof PropositionalTerm);
            ((PropositionalTerm) term).getTerms(result, done);
        }

        done.add(this);
    }
}
