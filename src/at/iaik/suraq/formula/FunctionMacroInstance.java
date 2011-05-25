/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Map;

import at.iaik.suraq.exceptions.InvalidParametersException;
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
            if (!paramMap.get(parameter).equals(macro.getParamType(parameter)))
                throw new InvalidParametersException(
                        "Type mismatch for parameter " + parameter.toString());
        }

        this.macro = macro;
        this.paramMap = paramMap;
    }

}
