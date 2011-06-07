/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Collection;

/**
 * 
 * A formula that is the xor of other formulas.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class XorFormula extends AndOrXorFormula {

    /**
     * 
     * Constructs a new <code>XorFormula</code>, consisting of the xor of the
     * given formulas.
     * 
     * @param formulas
     *            the formulas to xor.
     */
    public XorFormula(Collection<Formula> formulas) {
        super(formulas);
    }
}
