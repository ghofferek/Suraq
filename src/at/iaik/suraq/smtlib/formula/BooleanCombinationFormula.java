/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.Collection;
import java.util.Set;

import at.iaik.suraq.sexp.Token;

/**
 * A class for Boolean combination of formulas.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class BooleanCombinationFormula implements Formula {
    // just for type safety. No actual methods on this level.

    /**
     * 
     */
    private static final long serialVersionUID = 4161264962277332754L;

    /**
     * Returns a collection of subformulas of this
     * <code>BoolenCombinationFormula</code>.
     * 
     * @return a collection of subformulas of this
     *         <code>BoolenCombinationFormula</code>.
     */
    public abstract Collection<Formula> getSubFormulas();

    /**
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.toSmtlibV2().toString();
    }


}
