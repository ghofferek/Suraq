/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * 
 * A formula that is a conjunction of other formulas.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class AndFormula extends BooleanCombinationFormula {

    /**
     * The list of conjuncted formulas.
     */
    private final List<Formula> formulas;

    /**
     * 
     * Constructs a new <code>AndFormula</code>, consisting of the conjunction
     * of the given formulas.
     * 
     * @param formulas
     *            the formulas to conjunct.
     */
    public AndFormula(Collection<Formula> formulas) {
        this.formulas = new ArrayList<Formula>();
        this.formulas.addAll(formulas);
    }

    /**
     * Returns a collection of the conjuncted formulas.
     * 
     * @return a collection of the conjuncted formulas. (Copy)
     */
    public Collection<Formula> getConjuncts() {
        return new ArrayList<Formula>(formulas);
    }

    /**
     * @see at.iaik.suraq.formula.BooleanCombinationFormula#getSubFormulas()
     */
    @Override
    public Collection<Formula> getSubFormulas() {
        return new ArrayList<Formula>(formulas);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        List<Formula> subformulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            subformulas.add(formula.deepFormulaCopy());
        return new AndFormula(subformulas);
    }
}
