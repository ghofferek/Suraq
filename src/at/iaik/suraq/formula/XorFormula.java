/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * 
 * A formula that is the xor of other formulas.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class XorFormula extends BooleanCombinationFormula {

    /**
     * The list of xored formulas.
     */
    private final List<Formula> formulas;

    /**
     * 
     * Constructs a new <code>XorFormula</code>, consisting of the xor of the
     * given formulas.
     * 
     * @param formulas
     *            the formulas to xor.
     */
    public XorFormula(Collection<Formula> formulas) {
        this.formulas = new ArrayList<Formula>();
        this.formulas.addAll(formulas);
    }

    /**
     * @see at.iaik.suraq.formula.BooleanCombinationFormula#getSubFormulas()
     */
    @Override
    public Collection<Formula> getSubFormulas() {
        return new ArrayList<Formula>(formulas);
    }
}
