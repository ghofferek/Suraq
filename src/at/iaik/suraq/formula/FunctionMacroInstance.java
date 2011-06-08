/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.InvalidParametersException;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class FunctionMacroInstance implements Formula {

    /**
     * The macro of which this is an instance.
     */
    private final FunctionMacro macro;

    /**
     * A map from parameter names to the terms.
     */
    private final Map<Token, Term> paramMap;

    /**
     * Constructs a new <code>FunctionMacroInstance</code>.
     * 
     * @param macro
     *            the function macro of which this will be an instance.
     * @param paramMap
     *            the map from parameter names to their terms
     * @throws InvalidParametersException
     *             if the given map either misses a parameter or the type of the
     *             term in the map disagrees with the macro.
     */
    public FunctionMacroInstance(FunctionMacro macro, Map<Token, Term> paramMap)
            throws InvalidParametersException {

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
    public FunctionMacro getMacro() {
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
        FunctionMacro macro = new FunctionMacro(this.macro);
        Map<Token, Term> paramMap = new HashMap<Token, Term>();
        for (Token token : this.paramMap.keySet())
            paramMap.put((Token) token.deepCopy(), this.paramMap.get(token)
                    .deepTermCopy());

        try {
            return new FunctionMacroInstance(macro, paramMap);
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
        return new FunctionMacroInstance(macro.negationNormalForm(), paramMap);
    }

}
