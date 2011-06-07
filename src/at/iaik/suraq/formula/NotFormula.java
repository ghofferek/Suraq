/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

/**
 * A formula representing the negation of another one.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class NotFormula extends BooleanCombinationFormula {

    /**
     * The negated internal formula.
     */
    private final Formula formula;

    /**
     * 
     * Constructs a new <code>NotFormula</code>.
     * 
     * @param formula
     *            the negation of this formula.
     */
    public NotFormula(Formula formula) {
        this.formula = formula;
    }

    /**
     * @see at.iaik.suraq.formula.BooleanCombinationFormula#getSubFormulas()
     */
    @Override
    public Collection<Formula> getSubFormulas() {
        List<Formula> list = new ArrayList<Formula>();
        list.add(formula);
        return list;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return new NotFormula(formula.deepFormulaCopy());
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getSetOfArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getSetOfArrayVariables() {
        return formula.getSetOfArrayVariables();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getSetOfDomainVariables()
     */
    @Override
    public Set<DomainVariable> getSetOfDomainVariables() {
        return formula.getSetOfDomainVariables();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getSetOfPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getSetOfPropositionalVariables() {
        return formula.getSetOfPropositionalVariables();
    }
}
