/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.Token;

/**
 * 
 * This represents formulas in the fragment introduced in the MemoCODE'11 paper.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public interface Formula {

    /**
     * Returns a deep copy of the formula.
     * 
     * @return a deep copy of the formula
     */
    public Formula deepFormulaCopy();

    /**
     * Returns a set of all array variables used in this formula.
     * 
     * @return a set of array variables used in this formula.
     */
    public Set<ArrayVariable> getArrayVariables();

    /**
     * Returns a set of all domain variables used in this formula.
     * 
     * @return a set of domain variables used in this formula.
     */
    public Set<DomainVariable> getDomainVariables();

    /**
     * Returns a set of all propositional variables used in this formula.
     * 
     * @return a set of propositional variables used in this formula.
     */
    public Set<PropositionalVariable> getPropositionalVariables();

    /**
     * Returns a set of all uninterpreted function names used in this formula.
     * 
     * @return a set of uninterpreted function names used in this formula.
     */
    public Set<String> getUninterpretedFunctionNames();

    /**
     * Returns a set of all function macro names used in this formula.
     * 
     * @return a set of function macro names used in this formula.
     */
    public Set<String> getFunctionMacroNames();

    /**
     * Computes the index set of this formula. (Cf. Bradley/Manna, p. 295) The
     * set does <em>not</em> yet include the new variable <code>lambda</code>.
     * 
     * @return the index set.
     * @throws SuraqException
     *             if the formula contains array write expressions, or
     *             computation otherwise fails.
     */
    public Set<DomainTerm> getIndexSet() throws SuraqException;

    /**
     * Returns a copy of this formula in negation normal form.
     * 
     * @return a copy of this formula in negation normal form.
     * @throws SuraqException
     *             if the formula cannot be converted to NNF, e.g. due to
     *             resulting invalid array properties.
     */
    public Formula negationNormalForm() throws SuraqException;

    /**
     * Returns a new formula that is a version of this formula, with
     * substitutions performed according to the givem map. E.g., the local terms
     * of a function macro's body are converted to the (more) global terms of
     * the macro's instance. Terms which are not found in the map are returned
     * unchanged.
     * 
     * @param paramMap
     *            the map to convert local terms to the caller's scope
     * @return a (new) formula, converted according to the given map.
     */
    public Formula substituteFormula(Map<Token, Term> paramMap);

    /**
     * Replaces all array equalities in this formula by equivalent array
     * properties.
     */
    public void removeArrayEqualities();

    /**
     * Reduces all array properties in this formula to finite conjunctions over
     * the given index set. The index set must already include the special
     * variable lambda.
     * 
     * @param indexSet
     *            the index set.
     */
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet);
}
