/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;

/**
 * 
 * This class represents array terms. An array term is either an array variable,
 * or an array write expression.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class ArrayTerm extends Term {

    /**
     * @see at.iaik.suraq.formula.Term#getType()
     */
    @Override
    public SExpression getType() {
        return SExpressionConstants.ARRAY_TYPE;
    }

}
