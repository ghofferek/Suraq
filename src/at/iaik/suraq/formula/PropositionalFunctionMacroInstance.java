/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.InvalidParametersException;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalFunctionMacroInstance implements Formula {

    /**
     * The macro of which this is an instance.
     */
    private final PropositionalFunctionMacro macro;

    /**
     * A map from parameter names to the terms.
     */
    private final Map<Token, Term> paramMap;

    /**
     * Constructs a new <code>PropositionalFunctionMacroInstance</code>.
     * 
     * @param macro
     *            the function macro of which this will be an instance.
     * @param paramMap
     *            the map from parameter names to their terms
     * @throws InvalidParametersException
     *             if the given map either misses a parameter or the type of the
     *             term in the map disagrees with the macro.
     */
    public PropositionalFunctionMacroInstance(PropositionalFunctionMacro macro,
            Map<Token, Term> paramMap) throws InvalidParametersException {

        for (Token parameter : macro.getParameters()) {
            if (!paramMap.containsKey(parameter))
                throw new InvalidParametersException(
                        "Given map misses parameter " + parameter.toString());
            if (!paramMap.get(parameter).getType()
                    .equals(macro.getParamType(parameter)))
                throw new InvalidParametersException(
                        "Type mismatch for parameter " + parameter.toString());
        }

        this.macro = macro;
        this.paramMap = paramMap;
    }

    /**
     * Returns the macro of which this is an instance.
     * 
     * @return the <code>macro</code>
     */
    public PropositionalFunctionMacro getMacro() {
        return macro;
    }

    /**
     * Returns the term corresponding to the parameter <code>token</code>.
     * 
     * @param token
     *            the token identifying the parameter of which the term should
     *            be returned.
     * @return the term mapped to by the given token.
     */
    public Term getTerm(Token token) {
        return paramMap.get(token);
    }

    /**
     * Returns a copy of the parameter map.
     * 
     * @return the <code>paramMap</code>
     */
    public Map<Token, Term> getParamMap() {
        return new HashMap<Token, Term>(paramMap);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        PropositionalFunctionMacro macro = new PropositionalFunctionMacro(
                this.macro);
        Map<Token, Term> paramMap = new HashMap<Token, Term>();
        for (Token token : this.paramMap.keySet())
            paramMap.put((Token) token.deepCopy(), this.paramMap.get(token)
                    .deepTermCopy());

        try {
            return new PropositionalFunctionMacroInstance(macro, paramMap);
        } catch (InvalidParametersException exc) {
            // This should never happen!
            assert (false);
            throw new RuntimeException(
                    "Unexpected situation while copying function macro instance.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> variables = new HashSet<ArrayVariable>();
        for (Term term : paramMap.values())
            variables.addAll(term.getArrayVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> variables = new HashSet<DomainVariable>();
        for (Term term : paramMap.values())
            variables.addAll(term.getDomainVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> variables = new HashSet<PropositionalVariable>();
        for (Term term : paramMap.values())
            variables.addAll(term.getPropositionalVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        Map<Token, Term> paramMap = new HashMap<Token, Term>(this.paramMap);
        return new PropositionalFunctionMacroInstance(
                macro.negationNormalForm(), paramMap);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> functionNames = new HashSet<String>();
        functionNames.addAll(macro.getBody().getUninterpretedFunctionNames());
        for (Term term : paramMap.values())
            functionNames.addAll(term.getUninterpretedFunctionNames());
        return functionNames;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> macroNames = new HashSet<String>();
        macroNames.add(macro.getName().toString());
        for (Term term : paramMap.values())
            macroNames.addAll(term.getFunctionMacroNames());
        macroNames.addAll(macro.getBody().getFunctionMacroNames());
        return macroNames;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> macros = new HashSet<FunctionMacro>();
        macros.add(macro);
        for (Term term : paramMap.values())
            macros.addAll(term.getFunctionMacros());
        macros.addAll(macro.getBody().getFunctionMacros());
        return macros;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof PropositionalFunctionMacroInstance))
            return false;
        return ((PropositionalFunctionMacroInstance) obj).macro.equals(macro)
                && ((PropositionalFunctionMacroInstance) obj).paramMap
                        .equals(paramMap);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return macro.hashCode() ^ paramMap.hashCode();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> localIndexSet = macro.getBody().getIndexSet();
        Set<DomainTerm> result = new HashSet<DomainTerm>();
        for (DomainTerm term : localIndexSet) {
            result.add((DomainTerm) term.substituteTerm(paramMap));
        }
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#substituteFormula(java.util.Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, Term> paramMap) {
        Map<Token, Term> convertedMap = new HashMap<Token, Term>();

        for (Token token : this.paramMap.keySet())
            convertedMap.put(token,
                    this.paramMap.get(token).substituteTerm(paramMap));

        try {
            return new PropositionalFunctionMacroInstance(macro, convertedMap);
        } catch (InvalidParametersException exc) {
            throw new RuntimeException(
                    "Unexpected exception while converting PropositionalFunctionMacroInstance to caller scope.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.formula.Formula#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        macro.removeArrayEqualities();
        for (Term term : paramMap.values())
            term.removeArrayEqualities();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */

    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        macro.arrayPropertiesToFiniteConjunctions(indexSet);
        for (Term term : paramMap.values())
            term.arrayPropertiesToFiniteConjunctions(indexSet);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        macro.simplify();

        Boolean simplification = macro.simplify(paramMap);
        if (simplification != null)
            return new PropositionalConstant(simplification);

        return this;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        return macro.getBody().substituteFormula(paramMap).flatten();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        List<SExpression> expr = new ArrayList<SExpression>();
        expr.add(macro.getName());
        for (Token param : macro.getParameters())
            expr.add(paramMap.get(param).toSmtlibV2());
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#removeArrayWrites(at.iaik.suraq.formula.Formula)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        Set<Formula> localConstraints = macro.removeArrayWrites(
                topLevelFormula, noDependenceVars);
        for (Formula localConstraint : localConstraints)
            constraints.add(localConstraint.substituteFormula(paramMap));
        for (Term term : paramMap.values())
            term.removeArrayWrites(topLevelFormula, constraints,
                    noDependenceVars);

    }

    /**
     * @see at.iaik.suraq.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        macro.arrayReadsToUninterpretedFunctions(noDependenceVars);
        for (Token key : paramMap.keySet()) {
            Term term = paramMap.get(key);
            if (term instanceof ArrayRead)
                paramMap.put(key, ((ArrayRead) term)
                        .toUninterpretedFunctionInstance(noDependenceVars));
            else
                term.arrayReadsToUninterpretedFunctions(noDependenceVars);
        }
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        return macro.getUninterpretedFunctions();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.formula.UninterpretedFunction)
     */
    @Override
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        macro.substituteUninterpretedFunction(oldFunction, newFunction);
        for (Term param : paramMap.values())
            param.substituteUninterpretedFunction(oldFunction, newFunction);
    }

}
