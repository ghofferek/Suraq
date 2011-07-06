/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.sexp;

/**
 * 
 * This class bundles some important SExpression constants.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class SExpressionConstants {

    public static final SExpression ARRAY_TYPE = SExpression
            .fromString("(Array Value Value)");

    public static final Token VALUE_TYPE = (Token) SExpression
            .fromString("Value");

    public static final Token CONTROL_TYPE = (Token) SExpression
            .fromString("Control");

    public static final Token BOOL_TYPE = (Token) SExpression
            .fromString("Bool");

    public static final Token DECLARE_FUN = (Token) SExpression
            .fromString("declare-fun");

    public static final Token DEFINE_FUN = (Token) SExpression
            .fromString("define-fun");

    public static final Token ASSERT = (Token) SExpression.fromString("assert");

    public static final SExpression SET_LOGIC_SURAQ = SExpression
            .fromString("(set-logic Suraq)");

    public static final Token TRUE = (Token) SExpression.fromString("true");

    public static final Token FALSE = (Token) SExpression.fromString("false");

    public static final Token AND = (Token) SExpression.fromString("and");

    public static final Token OR = (Token) SExpression.fromString("or");

    public static final Token XOR = (Token) SExpression.fromString("xor");

    public static final Token NOT = (Token) SExpression.fromString("not");

    public static final Token DISTINCT = (Token) SExpression
            .fromString("distinct");

    public static final Token EQUAL = (Token) SExpression.fromString("=");

    public static final Token ITE = (Token) SExpression.fromString("ite");

    public static final Token IMPLIES = (Token) SExpression.fromString("=>");

    public static final Token FORALL = (Token) SExpression.fromString("forall");

    public static final Token SELECT = (Token) SExpression.fromString("select");

    public static final Token STORE = (Token) SExpression.fromString("store");

    public static final Token NO_DEPENDENCE = (Token) SExpression
            .fromString(":no_dependence");

}
