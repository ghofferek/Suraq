/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;

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

}
