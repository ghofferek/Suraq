/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Collection;

import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;

/**
 * 
 * This class represents domain terms. A domain term is either a domain
 * variable, (a domain constant,) an array read expression, or a function call.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class DomainTerm extends Term {

    /**
     * Checks whether this term consists of evars (with respect to the given
     * list of uvars) only.
     * 
     * @param uVars
     *            a collection of uvars.
     * @return <code>true</code> if this term consists of evars only,
     *         <code>false</code> otherwise.
     */
    public abstract boolean isEvar(Collection<DomainVariable> uVars);

    /**
     * @see at.iaik.suraq.formula.Term#getType()
     */
    @Override
    public SExpression getType() {
        return SExpressionConstants.VALUE_TYPE;
    }

}
