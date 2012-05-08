/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.exceptions.WrongFunctionTypeException;
import at.iaik.suraq.exceptions.WrongNumberOfParametersException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.util.Util;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class UninterpretedPredicateInstance implements Formula {

    /**
     * The function of which this is an instance.
     */
    private UninterpretedFunction function;

    /**
     * The list of parameters of this instance.
     */
    private final List<DomainTerm> parameters;

    /**
     * Constructs a new <code>UninterpretedPredicateInstance</code> with the
     * given values.
     * 
     * @param function
     *            the function that is applied.
     * @param parameters
     *            the parameters of the function
     * 
     * @throws WrongNumberOfParametersException
     *             if the number of parameters of the function does not match
     *             the size of <code>parameters</code>.
     * @throws WrongFunctionTypeException
     *             if the type of the given function is not <code>Value</code>.
     */
    public UninterpretedPredicateInstance(UninterpretedFunction function,
            List<DomainTerm> parameters)
            throws WrongNumberOfParametersException, WrongFunctionTypeException {
        if (function.getNumParams() != parameters.size())
            throw new WrongNumberOfParametersException();
        this.function = function;
        if (!function.getType().equals(SExpressionConstants.BOOL_TYPE))
            throw new WrongFunctionTypeException(
                    "Expected a domain function. Received type: "
                            + function.getType().toString());
        this.parameters = new ArrayList<DomainTerm>(parameters);
    }

    /**
     * Returns the function of which this is an instance
     * 
     * @return the <code>function</code>
     */
    public UninterpretedFunction getFunction() {
        return function;
    }

    /**
     * Returns a copy of the list of parameters of this instance.
     * 
     * @return the <code>parameters</code> (copy)
     */
    public List<DomainTerm> getParameters() {
        return new ArrayList<DomainTerm>(parameters);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public UninterpretedPredicateInstance deepFormulaCopy() {
        List<DomainTerm> parameterCopies = new ArrayList<DomainTerm>();
        for (DomainTerm term : parameters)
            parameterCopies.add(term.deepTermCopy());
        try {
            return new UninterpretedPredicateInstance(
                    new UninterpretedFunction(function), parameterCopies);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected situation whily copying predicate.", exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> variables = new HashSet<ArrayVariable>();
        for (Term term : parameters)
            variables.addAll(term.getArrayVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> variables = new HashSet<DomainVariable>();
        for (Term term : parameters)
            variables.addAll(term.getDomainVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> variables = new HashSet<PropositionalVariable>();
        for (Term term : parameters)
            variables.addAll(term.getPropositionalVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = new HashSet<String>();
        result.add(function.getName().toString());
        for (Term term : parameters)
            result.addAll(term.getUninterpretedFunctionNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = new HashSet<String>();
        for (Term term : parameters)
            result.addAll(term.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = new HashSet<FunctionMacro>();
        for (Term term : parameters)
            result.addAll(term.getFunctionMacros());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> result = new HashSet<DomainTerm>();
        for (DomainTerm term : parameters) {
            result.addAll(term.getIndexSet());
        }
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        return deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(java.util.Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, Term> paramMap) {
        List<DomainTerm> convertedParameters = new ArrayList<DomainTerm>();
        for (int count = 0; count < parameters.size(); count++)
            convertedParameters.add((DomainTerm) parameters.get(count)
                    .substituteTerm(paramMap));

        UninterpretedPredicateInstance result;
        try {
            result = new UninterpretedPredicateInstance(function,
                    convertedParameters);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected error while subsituting parameters.", exc);
        }
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(at.iaik.suraq.sexp.Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        if (function.getName().equals(oldFunction)) {
            function = newFunction;
            assert (newFunction.getType()
                    .equals(SExpressionConstants.BOOL_TYPE));
        }
        for (Term term : parameters)
            term.substituteUninterpretedFunction(oldFunction, newFunction);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        for (Term param : parameters)
            param.removeArrayEqualities();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        for (Term param : parameters)
            param.arrayPropertiesToFiniteConjunctions(indexSet);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        return deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public UninterpretedPredicateInstance flatten() {
        List<DomainTerm> flattenedParams = new ArrayList<DomainTerm>();
        for (DomainTerm term : parameters)
            flattenedParams.add((DomainTerm) term.flatten());
        try {
            return new UninterpretedPredicateInstance(function, flattenedParams);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected error while flattening UninterpretedFunctionInstance.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        List<SExpression> expr = new ArrayList<SExpression>();
        expr.add(function.getName());
        for (DomainTerm term : parameters)
            expr.add(term.toSmtlibV2());
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        for (Term param : parameters)
            param.removeArrayWrites(topLevelFormula, constraints,
                    noDependenceVars);

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions(java.util.Set)
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        for (DomainTerm term : parameters)
            if (term instanceof ArrayRead) {
                int index = parameters.indexOf(term);
                parameters.set(index, ((ArrayRead) term)
                        .toUninterpretedFunctionInstance(noDependenceVars));
            } else
                term.arrayReadsToUninterpretedFunctions(noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        Set<UninterpretedFunction> result = new HashSet<UninterpretedFunction>();
        result.add(function);
        for (Term term : parameters)
            result.addAll(term.getUninterpretedFunctions());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public void makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        for (Term param : parameters)
            param.makeArrayReadsSimple(topLevelFormula, constraints,
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
        PropositionalVariable newVar = new PropositionalVariable(
                Util.freshVarName(topLeveFormula, "aux"));
        List<PropositionalTerm> terms = new ArrayList<PropositionalTerm>();
        terms.add(newVar);
        terms.add(new FormulaTerm(this.deepFormulaCopy()));
        constraints.add(new PropositionalEq(terms, true));

        if (Util.formulaContainsAny(this, noDependenceVars))
            noDependenceVars.add(new Token(newVar.getVarName()));

        return newVar;
    }

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getAssertPartition() {
        Set<Integer> partitions = function.getAssertPartition();

        for (DomainTerm term : parameters)
            partitions.addAll(term.getAssertPartition());

        return partitions;
    }
    
    
    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformFormulaToConsequentsFormula(at.iaik.suraq.smtlib.formula.Formula)
     */
	@Override
	public Formula transformToConsequentsForm(Formula formula) {
		return transformToConsequentsForm(formula, false, true);
	}
	
    /** 
     * Transforms formula to formula for consequents.
     * Formulas for consequents should have the following structure:
     *  		- each atom is either a positive equality of two terms, a propositional variable,
     *  			or an uninterpreted predicate
     *   		- each literal is either an atom or a negation of an atom
     *   		- formula is always an or formula which consists of at least one literal 
     *   
     * @param fomrula
     * 			to be transformed into a consequents formula 
     * @param notFlag
     * 			indicates if number of not operations occurred so far is even or odd 
     * 			(notFlag=true equates to odd number)
     * @param firstLevel
     * 			indicates if function call appeared in the first recursion step
     * @return the new transformed formula is possible, if not null
     *  	 
     */
	
	@Override
    public Formula transformToConsequentsForm(Formula formula, boolean notFlag, boolean firstLevel) {

        UninterpretedPredicateInstance uip;
        
        List<DomainTerm> parameterCopies = new ArrayList<DomainTerm>();
        for (DomainTerm term : parameters)
            parameterCopies.add(term.deepTermCopy());
        
        try {
        	uip = new UninterpretedPredicateInstance(
        			new UninterpretedFunction(function), parameterCopies);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected error while creating new uninterpreted predicate", exc);
        }
		
        if (firstLevel==true){				

			List<Formula> literals = new ArrayList<Formula>(); 
			literals.add(uip);
			Formula orFormula = new OrFormula(literals);
			return	orFormula;	
		}
        return uip;

	}

}
