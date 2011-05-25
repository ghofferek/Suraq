/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * 
 * A formula that is a disjunction of other formulas.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class OrFormula extends BooleanCombinationFormula {

    /**
     * The list of disjuncted formulas.
     */
    private final List<Formula> formulas;

    /**
     * 
     * Constructs a new <code>OrFormula</code>, consisting of the disjunction of
     * the given formulas.
     * 
     * @param formulas
     *            the formulas to disjunct.
     */
    public OrFormula(Collection<Formula> formulas) {
        this.formulas = new ArrayList<Formula>();
        this.formulas.addAll(formulas);
    }

    /**
     * Returns a collection of the disjuncted formulas.
     * 
     * @return a collection of the disjuncted formulas. (Copy)
     */
    public Collection<Formula> getDisjuncts() {
        return new ArrayList<Formula>(formulas);
    }

    /**
     * @see at.iaik.suraq.formula.BooleanCombinationFormula#getSubFormulas()
     */
    @Override
    public Collection<Formula> getSubFormulas() {
        return new ArrayList<Formula>(formulas);
    }
}
