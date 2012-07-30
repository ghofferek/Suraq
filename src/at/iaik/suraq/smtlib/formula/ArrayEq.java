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

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.util.Util;

/**
 * A formula consisting of the (in)equality of array terms.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayEq extends EqualityFormula {

    /**
     * 
     */
    private static final long serialVersionUID = 6969625051610060136L;

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
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        List<ArrayTerm> terms = new ArrayList<ArrayTerm>();
        for (Term term : this.terms) {
            terms.add((ArrayTerm) term.deepTermCopy());
        }
        return new ArrayEq(terms, equal);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.EqualityFormula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        throw new SuraqException(
                "Encountered array equality while computing index set. Should have already been removed.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.EqualityFormula#removeArrayEqualitiesTerm()
     */
    @Override
    public Formula removeArrayEqualities() {
        throw new RuntimeException(
                "Cannot remove array equalities from an array equality.");
    }

    /**
     * Returns an equivalent formula consisting of (an) array property(s).
     * 
     * @return an equivalent formula consisting of (an) array property(s).
     */
    public Formula toArrayProperties() {
        Formula newFormula;
        DomainVariable index = DomainVariable.create(Util.freshVarName(this,
                "index"));
        Set<DomainVariable> uVars = new HashSet<DomainVariable>();
        uVars.add(index);
        if (equal) {
            List<ArrayRead> arrayReads = new ArrayList<ArrayRead>();
            for (Term term : terms)
                arrayReads.add(new ArrayRead((ArrayTerm) term, index));
            try {
                newFormula = new ArrayProperty(uVars,
                        new PropositionalConstant(true), new DomainEq(
                                arrayReads, true));
            } catch (SuraqException exc) {
                throw new RuntimeException(
                        "Unexptected exception while creatin array property to remove array equality.",
                        exc);
            }
        } else { // in case of disequality, make property for each pair.
            List<Formula> conjuncts = new ArrayList<Formula>();
            for (int i = 0; i < terms.size(); i++) {
                for (int j = i + 1; i < terms.size(); j++) {
                    List<ArrayRead> arrayReads = new ArrayList<ArrayRead>();
                    arrayReads.add(new ArrayRead((ArrayTerm) terms.get(i),
                            index));
                    arrayReads.add(new ArrayRead((ArrayTerm) terms.get(j),
                            index));
                    try {
                        conjuncts.add(new ArrayProperty(uVars,
                                new PropositionalConstant(true), new DomainEq(
                                        arrayReads, true)));
                    } catch (SuraqException exc) {
                        throw new RuntimeException(
                                "Unexptected exception while creatin array property to remove array equality.",
                                exc);
                    }
                }
            }
            newFormula = AndFormula.generate(conjuncts);
        }
        return newFormula;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        throw new RuntimeException(
                "arrayPropertiesToFiniteConjunctions cannot be called on an ArrayEq.\nRemove array equalities before reducing properties to conjunctions.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.EqualityFormula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        List<Term> pairs = new ArrayList<Term>();
        for (Term term : terms) {
            if (term instanceof ArrayWrite) {
                pairs.add(((ArrayWrite) term).applyWriteAxiom(topLevelFormula,
                        constraints, noDependenceVars));
            } else {
                pairs.add(term.removeArrayWritesTerm(topLevelFormula, constraints,
                        noDependenceVars));
            }
        }
        try {
            return create(pairs, equal);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm()
     */
    @Override
    public OrFormula transformToConsequentsForm() {
        throw new RuntimeException(
                "transformToConsequentsForm cannot be called on an ArrayEq.\nArrays should be removed by now.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm(boolean,
     *      boolean)
     */
    @Override
    public Formula transformToConsequentsForm(boolean notFlag,
            boolean firstLevel) {
        throw new RuntimeException(
                "transformToConsequentsForm cannot be called on an ArrayEq.\nArrays should be removed by now.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.Map)
     */
    @Override
    public PropositionalVariable tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding) {
        throw new RuntimeException(
                "Array equalities should have been removed before Tseitin encoding!");
    }
    
    

    @Override
    public Formula replaceEquivalences(Formula topLeveFormula, Map<EqualityFormula, String> replacements, Set<Token> noDependenceVars)
    {
        throw new RuntimeException(
                "ArrayEq cannot be called on an UninterpretedFunctions.\n"
                        + "ArrayEq should be removed by now.");
    }

    public Formula removeDomainITE(Formula topLevelFormula, Set<Token> noDependenceVars)
    {
        throw new RuntimeException("Arrays must be replaced removing DomainITE.");
    }
}
