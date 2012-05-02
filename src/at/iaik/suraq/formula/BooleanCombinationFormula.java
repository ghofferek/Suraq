/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * A class for Boolean combination of formulas.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class BooleanCombinationFormula implements Formula {
    // just for type safety. No actual methods on this level.

	 /**
     * The assert-partitions
     */
	protected List<Integer> assertPartitions = new ArrayList<Integer>();
	
	
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
    
    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    public List<Integer> getAssertPartition(){
    	return this.assertPartitions;
    }
}
