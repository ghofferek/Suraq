/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;

/**
 * 
 * A formula that is a conjunction of other formulas.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class AndFormula extends AndOrXorFormula {

    /**
     * 
     * Constructs a new <code>AndFormula</code>, consisting of the conjunction
     * of the given formulas.
     * 
     * @param formulas
     *            the formulas to conjunct.
     */
    public AndFormula(Collection<Formula> formulas) {
        super(formulas);
    }

    /**
     * Returns a collection of the conjuncted formulas.
     * 
     * @return a collection of the conjuncted formulas. (Copy)
     */
    public Collection<Formula> getConjuncts() {
        return new ArrayList<Formula>(formulas);
    }

}
