/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.InvalidIndexGuardException;
import at.iaik.suraq.exceptions.InvalidValueConstraintException;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.util.Util;

/**
 * 
 * This class represents an array property. See the book of Bradley & Manna
 * "The Calculus of Computation" for more details on array properties.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayProperty implements Formula {

    /**
     * The collection of universally quantified variables.
     */
    private final List<DomainVariable> uVars;

    /**
     * The formula representing the index guard.
     */
    private final Formula indexGuard;

    /**
     * The formula representing the values constraint.
     */
    private final Formula valueConstraint;

    /**
     * 
     * Constructs a new <code>ArrayProperty</code> with the given values.
     * 
     * @param uVars
     *            the collection of universally quantified variables.
     * @param indexGuard
     *            the index guard.
     * @param valueConstraint
     *            the value constraint.
     * @throws InvalidIndexGuardException
     *             if the index guard does not adhere to the grammar
     * @throws InvalidValueConstraintException
     *             if the value constraint does not adhere to the grammar.
     */
    public ArrayProperty(Collection<DomainVariable> uVars, Formula indexGuard,
            Formula valueConstraint) throws InvalidIndexGuardException,
            InvalidValueConstraintException {
        this.uVars = new ArrayList<DomainVariable>(uVars);

        if (!ArrayProperty.checkIndexGuard(uVars, indexGuard))
            throw new InvalidIndexGuardException();

        if (!ArrayProperty.checkValueConstraint(uVars, valueConstraint))
            throw new InvalidValueConstraintException();

        this.indexGuard = indexGuard;
        this.valueConstraint = valueConstraint;
    }

    /**
     * Checks whether the given formula is a legal value constraint (w.r.t. the
     * given universally quantified variables).
     * 
     * @param uVars
     *            a list of universally quantified variables
     * @param valueConstraint
     *            the formula to check
     * @return <code>true</code> if the given formula is a legal value
     *         constraint w.r.t. the given list of universally quantified
     *         variables, <code>false</code> otherwise.
     */
    private static boolean checkValueConstraint(
            Collection<DomainVariable> uVars, Formula valueConstraint) {

        if (valueConstraint instanceof BooleanCombinationFormula) {
            for (Formula subFormula : ((BooleanCombinationFormula) valueConstraint)
                    .getSubFormulas()) {
                if (!ArrayProperty.checkValueConstraint(uVars, subFormula))
                    return false;
            }
            return true;
        }

        if (valueConstraint instanceof DomainEq) {

            for (DomainTerm term : ((DomainEq) valueConstraint)
                    .getDomainTerms()) {
                if (term instanceof ArrayRead) {
                    DomainTerm index = ((ArrayRead) term).getIndexTerm();
                    if (!(index instanceof DomainVariable))
                        return false;
                } else {
                    if (!term.isEvar(uVars))
                        return false;
                }
            }
            return true;
        }

        // something that is not a legal value constraint
        return false;
    }

    /**
     * Returns a set of all terms used as eVars in the index guard.
     * 
     * @param uVars
     *            a collection of uVars.
     * @param indexGuard
     *            the index guard (or a subformula of it)
     * @return the set of all terms that parse as evars in the given
     *         <code>indexGuard</code>.
     * @throws InvalidIndexGuardException
     *             if the given <code>indgexGuard</code> is not a valid one.
     *             (This method does not perform all checks; the exception is
     *             merely thrown when an invalid index guard is found
     *             "by chance".)
     */
    private static Set<DomainTerm> getEVarsFromIndexGuard(
            Collection<DomainVariable> uVars, Formula indexGuard)
            throws InvalidIndexGuardException {
        if (indexGuard instanceof PropositionalConstant)
            // only "true" is allowed in index guards
            return new HashSet<DomainTerm>();

        if (indexGuard instanceof AndFormula) {
            Set<DomainTerm> result = new HashSet<DomainTerm>();
            for (Formula formula : ((AndFormula) indexGuard).getConjuncts())
                result.addAll(ArrayProperty.getEVarsFromIndexGuard(uVars,
                        formula));
            return result;
        }

        if (indexGuard instanceof OrFormula) {
            Set<DomainTerm> result = new HashSet<DomainTerm>();
            for (Formula formula : ((OrFormula) indexGuard).getDisjuncts())
                result.addAll(ArrayProperty.getEVarsFromIndexGuard(uVars,
                        formula));
            return result;
        }

        if (indexGuard instanceof DomainEq) {
            Set<DomainTerm> result = new HashSet<DomainTerm>();
            List<DomainTerm> terms = ((DomainEq) indexGuard).getDomainTerms();
            for (int count = 0; count < terms.size(); count++) {
                if (terms.get(count) instanceof ArrayRead
                        || terms.get(count) instanceof DomainIte)
                    throw new InvalidIndexGuardException();

                if (terms.get(count).isEvar(uVars))
                    result.add(terms.get(count));

            }
            return result;
        }

        // something that is not an index guard.
        throw new InvalidIndexGuardException();
    }

    /**
     * Checks if the given formula is a valid index guard.
     * 
     * @param uVars
     *            the collection of universally quantified variables.
     * @param indexGuard
     *            the formula to check
     * @return <code>true</code> if the given <code>indexGuard</code> is a valid
     *         index guard, <code>false</code> otherwise.
     */
    private static boolean checkIndexGuard(Collection<DomainVariable> uVars,
            Formula indexGuard) {
        if (indexGuard instanceof PropositionalConstant)
            // only "true" is allowed in index guards
            return ((PropositionalConstant) indexGuard).getValue();

        if (indexGuard instanceof AndFormula) {
            for (Formula formula : ((AndFormula) indexGuard).getConjuncts())
                if (!ArrayProperty.checkIndexGuard(uVars, formula))
                    return false;
            return true;
        }

        if (indexGuard instanceof OrFormula) {

            for (Formula formula : ((OrFormula) indexGuard).getDisjuncts())
                if (!ArrayProperty.checkIndexGuard(uVars, formula))
                    return false;
            return true;
        }

        if (indexGuard instanceof DomainEq) {
            if (((DomainEq) indexGuard).isEqual())
                return true;
            else {
                List<DomainTerm> terms = ((DomainEq) indexGuard)
                        .getDomainTerms();
                for (int count = 0; count < terms.size(); count++) {
                    for (int inner_count = count + 1; inner_count < terms
                            .size(); inner_count++) {
                        if (terms.get(count) instanceof ArrayRead
                                || terms.get(count) instanceof DomainIte)
                            return false;
                        if (terms.get(inner_count) instanceof ArrayRead
                                || terms.get(inner_count) instanceof DomainIte)
                            return false;
                        if (!(terms.get(count).isEvar(uVars) || terms.get(
                                inner_count).isEvar(uVars)))
                            return false;
                    }
                }
                return true;
            }
        }

        // something that is not an index guard.
        return false;

    }

    /**
     * Returns a copy of the set of universally quantified variables.
     * 
     * @return the <code>uVars</code> (copy)
     */
    public Collection<DomainVariable> getuVars() {
        return new HashSet<DomainVariable>(uVars);
    }

    /**
     * Returns the index guard formula.
     * 
     * @return the <code>indexGuard</code>
     */
    public Formula getIndexGuard() {
        return indexGuard;
    }

    /**
     * Returns the value constraint formula.
     * 
     * @return the <code>valueConstraint</code>
     */
    public Formula getValueConstraint() {
        return valueConstraint;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        List<DomainVariable> uVars = new ArrayList<DomainVariable>();
        for (DomainVariable uVar : this.uVars)
            uVars.add((DomainVariable) uVar.deepTermCopy());
        try {
            return new ArrayProperty(uVars, indexGuard.deepFormulaCopy(),
                    valueConstraint.deepFormulaCopy());
        } catch (InvalidIndexGuardException exc) {
            // This should never happen!
            assert (false);
            throw new RuntimeException(
                    "Unexpected situation while copying array property.", exc);

        } catch (InvalidValueConstraintException exc) {
            // This should never happen!
            assert (false);
            throw new RuntimeException(
                    "Unexpected situation while copying array property.", exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        return valueConstraint.getArrayVariables();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> result = indexGuard.getDomainVariables();
        result.addAll(valueConstraint.getDomainVariables());
        result.removeAll(uVars);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> result = indexGuard
                .getPropositionalVariables();
        result.addAll(valueConstraint.getPropositionalVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        return new ArrayProperty(new ArrayList<DomainVariable>(uVars),
                indexGuard.negationNormalForm(),
                valueConstraint.negationNormalForm());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = indexGuard.getUninterpretedFunctionNames();
        result.addAll(valueConstraint.getUninterpretedFunctionNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = indexGuard.getFunctionMacroNames();
        result.addAll(valueConstraint.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = indexGuard.getFunctionMacros();
        result.addAll(valueConstraint.getFunctionMacros());
        return result;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof ArrayProperty))
            return false;
        ArrayProperty other = (ArrayProperty) obj;
        return other.uVars.equals(uVars) && other.indexGuard.equals(indexGuard)
                && other.valueConstraint.equals(valueConstraint);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return uVars.hashCode() ^ indexGuard.hashCode()
                ^ valueConstraint.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        return ArrayProperty.getEVarsFromIndexGuard(uVars, indexGuard);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(java.util.Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, Term> paramMap) {
        try {
            return new ArrayProperty(uVars,
                    indexGuard.substituteFormula(paramMap),
                    valueConstraint.substituteFormula(paramMap));
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unable to convert ArrayProperty to caller scope.", exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        // Nothing to do.
        // ArrayProperties cannot contain array equalities.
        return;
    }

    /**
     * Instantiates the body of this property by replacing the universally
     * quantified variables with the given terms.
     * 
     * @param indices
     *            the terms to use in place of the universally quantified
     *            variables.
     * @return an instance of this property's body with the given terms
     *         replacing universally quantified variables
     * @throws SuraqException
     *             if the number of indices does not match the number of
     *             <code>uVars</code>.
     */
    private Formula instantiate(List<DomainTerm> indices) throws SuraqException {
        if (indices.size() != uVars.size())
            throw new SuraqException(
                    "Wrong number of indices for instantiating array property");

        Map<Token, Term> substitutions = new HashMap<Token, Term>();
        for (int count = 0; count < uVars.size(); count++)
            substitutions.put(new Token(uVars.get(count).toString()),
                    indices.get(count));

        return new ImpliesFormula(indexGuard.substituteFormula(substitutions),
                valueConstraint.substituteFormula(substitutions));
    }

    /**
     * Returns a new formula that is the finite conjunction version of this
     * array property, instantiated over the given index set.
     * 
     * @param indexSet
     *            the index set.
     * @return the finite conjunction
     */
    public AndFormula toFiniteConjunction(Set<DomainTerm> indexSet) {
        assert (indexSet.size() > 0);
        List<Formula> conjuncts = new ArrayList<Formula>();
        List<DomainTerm> indices = new ArrayList<DomainTerm>(indexSet);
        List<Integer> counters = new ArrayList<Integer>();
        for (int count = 0; count < uVars.size(); count++)
            counters.add(0);
        do {
            List<DomainTerm> currentIndices = new ArrayList<DomainTerm>();
            for (int count = 0; count < counters.size(); count++)
                currentIndices.add(indices.get(counters.get(count)));
            try {
                conjuncts.add(this.instantiate(currentIndices));
            } catch (SuraqException exc) {
                throw new RuntimeException(
                        "Unexpected exception while converting array property to finite conjunction.",
                        exc);
            }

        } while (Util.incrementCounters(counters, indices.size()));
        return new AndFormula(conjuncts);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        throw new RuntimeException(
                "arrayPropertiesToFiniteConjunctions cannot be called on an ArrayProperty.\nUse toFiniteConjunction instead.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        // Not needed, as array properties are removed before simplifications.
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        try {
            return new ArrayProperty(uVars, indexGuard.flatten(),
                    valueConstraint.flatten());
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unforseen exception while flattening array property.", exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        return new SExpression(SExpressionConstants.FORALL, uVarsExpression(),
                (new ImpliesFormula(indexGuard, valueConstraint)).toSmtlibV2());
    }

    /**
     * Returns an s-expression of all universally quantified variables and their
     * type. E.g. ((var1 Value)(var2 Value)(var3 Value)).
     * 
     * @return s-expression of uvars.
     */
    private SExpression uVarsExpression() {
        List<SExpression> expr = new ArrayList<SExpression>();
        for (DomainVariable uVar : uVars)
            expr.add(new SExpression(uVar.toSmtlibV2(),
                    SExpressionConstants.VALUE_TYPE));
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        // Does not contain array writes subformulas.
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        indexGuard.arrayReadsToUninterpretedFunctions(noDependenceVars);
        valueConstraint.arrayReadsToUninterpretedFunctions(noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        Set<UninterpretedFunction> result = indexGuard
                .getUninterpretedFunctions();
        result.addAll(valueConstraint.getUninterpretedFunctions());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        indexGuard.substituteUninterpretedFunction(oldFunction, newFunction);
        valueConstraint.substituteUninterpretedFunction(oldFunction,
                newFunction);
    }

    /**
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.toSmtlibV2().toString();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(Formula,
     *      java.util.Set, Set)
     */
    @Override
    public void makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        indexGuard.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
        valueConstraint.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        try {
            return new ArrayProperty(uVars,
                    indexGuard.uninterpretedPredicatesToAuxiliaryVariables(
                            topLeveFormula, constraints, noDependenceVars),
                    valueConstraint
                            .uninterpretedPredicatesToAuxiliaryVariables(
                                    topLeveFormula, constraints,
                                    noDependenceVars));
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpectedly unable to create ArrayProperty.", exc);
        }
    }

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = this.indexGuard.getPartitionsFromSymbols();
        partitions.addAll(this.valueConstraint.getPartitionsFromSymbols());

        for (DomainVariable var : uVars)
            partitions.addAll(var.getPartitionsFromSymbols());

        return partitions;
    }
    
    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm()
     */
	@Override
	public Formula transformToConsequentsForm() {
		throw new RuntimeException(
				"transformToConsequentsForm cannot be called on an ArrayProperty.\nArrays should be removed by now.");
	}
	
	 /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm(boolean, boolean)
     */	
	@Override
	public Formula transformToConsequentsForm(boolean notFlag, boolean firstLevel) {
		throw new RuntimeException(
				"transformToConsequentsForm cannot be called on an ArrayProperty.\nArrays should be removed by now.");
	}    
}
