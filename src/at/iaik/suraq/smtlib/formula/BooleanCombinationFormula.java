/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.Collection;

import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.IdGenerator;

/**
 * A class for Boolean combination of formulas.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class BooleanCombinationFormula implements Formula {

    /**
     * 
     */
    private static final long serialVersionUID = 4161264962277332754L;

    private final long id = IdGenerator.getId();

    /**
     * Returns a collection of subformulas of this
     * <code>BoolenCombinationFormula</code>.
     * 
     * @return a collection of subformulas of this
     *         <code>BooleanCombinationFormula</code>.
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

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getId()
     */
    @Override
    public long getId() {
        return id;
    }

    /**
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     */
    @Override
    public final int compareTo(SMTLibObject o) {
        long otherId = o.getId();
        if (this.id < otherId)
            return -1;
        if (this.id == otherId)
            return 0;
        if (this.id > otherId)
            return 1;
        throw new RuntimeException("Something is TERRIBLY wrong!!");
    }

}
