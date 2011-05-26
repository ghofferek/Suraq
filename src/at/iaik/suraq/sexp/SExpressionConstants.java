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

    public static final SExpression VALUE_TYPE = SExpression
            .fromString("Value");

    public static final SExpression CONTROL_TYPE = SExpression
            .fromString("Control");

    public static final SExpression BOOL_TYPE = SExpression.fromString("Bool");

    public static final SExpression DECLARE_FUN = SExpression
            .fromString("declare-fun");

    public static final SExpression DEFINE_FUN = SExpression
            .fromString("define-fun");

    public static final SExpression ASSERT = SExpression.fromString("assert");

    public static final SExpression SET_LOGIC_SURAQ = SExpression
            .fromString("(set-logic Suraq)");

    public static final SExpression TRUE = SExpression.fromString("true");

    public static final SExpression FALSE = SExpression.fromString("false");

    public static final SExpression AND = SExpression.fromString("and");

    public static final SExpression OR = SExpression.fromString("or");

    public static final SExpression XOR = SExpression.fromString("xor");

    public static final SExpression NOT = SExpression.fromString("not");

    public static final SExpression DISTINCT = SExpression
            .fromString("distinct");

    public static final SExpression EQUAL = SExpression.fromString("=");

    public static final SExpression ITE = SExpression.fromString("ite");

    public static final SExpression IMPLIES = SExpression.fromString("=>");

    public static final Object FORALL = SExpression.fromString("forall");

    public static final Object SELECT = SExpression.fromString("select");

    public static final Object STORE = SExpression.fromString("store");

}
