/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.exceptions.WrongNumberOfParametersException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * An instance of an uninterpreted function.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class UninterpretedFunctionInstance extends DomainTerm implements
        Formula {

    /**
     * The function of which this is an instance.
     */
    private UninterpretedFunction function;

    /**
     * The list of parameters of this instance.
     */
    private final List<DomainTerm> parameters;

    /**
     * Constructs a new <code>UninterpretedFunctionInstance</code> with the
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
     */
    public UninterpretedFunctionInstance(UninterpretedFunction function,
            List<DomainTerm> parameters)
            throws WrongNumberOfParametersException {
        if (function.getNumParams() != parameters.size())
            throw new WrongNumberOfParametersException();
        this.function = function;
        this.parameters = new ArrayList<DomainTerm>(parameters);
    }

    /**
     * Constructs a new <code>UninterpretedFunctionInstance</code> with just one
     * parameter.
     * 
     * @param function
     *            the function that is applied
     * @param term
     *            the single parameter of the function.
     * @throws WrongNumberOfParametersException
     *             if the number of parameters of the function does not match
     *             the size of <code>parameters</code>.
     */
    public UninterpretedFunctionInstance(UninterpretedFunction function,
            DomainTerm term) throws WrongNumberOfParametersException {
        if (function.getNumParams() != 1)
            throw new WrongNumberOfParametersException();
        this.function = function;
        List<DomainTerm> params = new ArrayList<DomainTerm>();
        params.add(term);
        this.parameters = params;
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
     * @see at.iaik.suraq.formula.DomainTerm#isEvar(java.util.Collection)
     */
    @Override
    public boolean isEvar(Collection<DomainVariable> uVars) {
        for (DomainTerm term : parameters) {
            if (!term.isEvar(uVars))
                return false;
        }
        return true;
    }

    /**
     * @see at.iaik.suraq.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        List<DomainTerm> parameters = new ArrayList<DomainTerm>();
        for (DomainTerm term : this.parameters)
            parameters.add((DomainTerm) term.deepTermCopy());
        try {
            return new UninterpretedFunctionInstance(new UninterpretedFunction(
                    function), parameters);
        } catch (WrongNumberOfParametersException exc) {
            // This should never happen!
            assert (false);
            throw new RuntimeException(
                    "Unexpected situation while copying uninterpreted function instance.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> variables = new HashSet<ArrayVariable>();
        for (Term term : parameters)
            variables.addAll(term.getArrayVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> variables = new HashSet<DomainVariable>();
        for (Term term : parameters)
            variables.addAll(term.getDomainVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> variables = new HashSet<PropositionalVariable>();
        for (Term term : parameters)
            variables.addAll(term.getPropositionalVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = new HashSet<String>();
        for (Term term : parameters)
            result.addAll(term.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = new HashSet<FunctionMacro>();
        for (Term term : parameters)
            result.addAll(term.getFunctionMacros());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getUninterpretedFunctionNames()
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
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof UninterpretedFunctionInstance))
            return false;
        UninterpretedFunctionInstance other = (UninterpretedFunctionInstance) obj;
        if (!other.parameters.equals(parameters))
            return false;
        if (!other.function.equals(function))
            return false;
        return true;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return function.hashCode() ^ parameters.hashCode();
    }

    /**
     * @see at.iaik.suraq.formula.Term#getIndexSet()
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
     * @see at.iaik.suraq.formula.Term#substituteTerm(java.util.Map)
     */
    @Override
    public Term substituteTerm(Map<Token, Term> paramMap) {
        List<DomainTerm> convertedParameters = new ArrayList<DomainTerm>();
        for (int count = 0; count < parameters.size(); count++)
            convertedParameters.add((DomainTerm) parameters.get(count)
                    .substituteTerm(paramMap));

        UninterpretedFunctionInstance result;
        try {
            result = new UninterpretedFunctionInstance(function,
                    convertedParameters);
        } catch (WrongNumberOfParametersException exc) {
            throw new RuntimeException(
                    "Unexpected error in number of parameters while trying to convert UninterpretedFunctionInstance to caller scope.",
                    exc);
        }
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#toSmtlibV2()
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
     * @see at.iaik.suraq.formula.Term#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        for (Term param : parameters)
            param.arrayPropertiesToFiniteConjunctions(indexSet);
    }

    /**
     * @see at.iaik.suraq.formula.Term#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        for (Term param : parameters)
            param.removeArrayEqualities();
    }

    /**
     * @see at.iaik.suraq.formula.Term#removeArrayWrites(at.iaik.suraq.formula.Formula)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        for (Term param : parameters)
            param.removeArrayWrites(topLevelFormula, constraints,
                    noDependenceVars);

    }

    /**
     * @see at.iaik.suraq.formula.Term#arrayReadsToUninterpretedFunctions()
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
     * @see at.iaik.suraq.formula.Term#getUninterpretedFunctions()
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
     * @see at.iaik.suraq.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.formula.UninterpretedFunction)
     */
    @Override
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        if (function.getName().equals(oldFunction))
            function = newFunction;
        for (Term term : parameters)
            term.substituteUninterpretedFunction(oldFunction, newFunction);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return (Formula) deepTermCopy();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        return this.deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#substituteFormula(java.util.Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, Term> paramMap) {
        return (Formula) substituteTerm(paramMap);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        return this.deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#flatten()
     */
    @Override
    public UninterpretedFunctionInstance flatten() {
        List<DomainTerm> flattenedParams = new ArrayList<DomainTerm>();
        for (DomainTerm term : parameters)
            flattenedParams.add((DomainTerm) term.flatten());
        try {
            return new UninterpretedFunctionInstance(function, flattenedParams);
        } catch (WrongNumberOfParametersException exc) {
            throw new RuntimeException(
                    "Unexpected error while flattening UninterpretedFunctionInstance.",
                    exc);
        }

    }

    /**
     * @see at.iaik.suraq.formula.Term#makeArrayReadsSimple(at.iaik.suraq.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public void makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        for (Term param : parameters)
            param.makeArrayReadsSimple(topLevelFormula, constraints,
                    noDependenceVars);
    }
}
