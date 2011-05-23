/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Map;

import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * This class represents a (Boolean) function macro. It represents the
 * "define-fun" part of the input. Do not confuse it with
 * <code>FunctionMacroInstance</code> which is an actual instance of a macro.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class FunctionMacro {

    /**
     * The name of this macro.
     */
    private final Token name;

    /**
     * The map of parameters to their types.
     */
    private final Map<Token, SExpression> paramMap;

    /**
     * The body of this macro.
     */
    private final Formula body;

    /**
     * Constructs a new <code>FunctionMacro</code> with the given values.
     * 
     * @param name
     *            the name of this macro.
     * @param paramMap
     *            the map from parameters to types.
     * @param body
     *            the actual body.
     */
    public FunctionMacro(Token name, Map<Token, SExpression> paramMap,
            Formula body) {
        this.name = name;
        this.paramMap = paramMap;
        this.body = body;
    }

    /**
     * @return the <code>name</code>
     */
    public Token getName() {
        return name;
    }

}
