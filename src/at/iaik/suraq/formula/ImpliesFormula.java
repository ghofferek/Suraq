/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

/**
 * A class for formulas of the form (a => b).
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ImpliesFormula extends BooleanCombinationFormula {

    /**
     * The left side of the implication.
     */
    private final Formula leftSide;

    /**
     * The right side of the implication.
     */
    private final Formula rightSide;

    /**
     * 
     * Constructs a new <code>ImpliesFormula</code>.
     * 
     * @param leftSide
     *            the left side of the implication
     * @param rightSide
     *            the right side of the implication
     */
    public ImpliesFormula(Formula leftSide, Formula rightSide) {
        this.leftSide = leftSide;
        this.rightSide = rightSide;
    }

    /**
     * @see at.iaik.suraq.formula.BooleanCombinationFormula#getSubFormulas()
     */
    @Override
    public Collection<Formula> getSubFormulas() {
        List<Formula> list = new ArrayList<Formula>();
        list.add(leftSide);
        list.add(rightSide);
        return list;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return new ImpliesFormula(leftSide.deepFormulaCopy(),
                rightSide.deepFormulaCopy());
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getSetOfArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getSetOfArrayVariables() {
        Set<ArrayVariable> result = leftSide.getSetOfArrayVariables();
        result.addAll(rightSide.getSetOfArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getSetOfDomainVariables()
     */
    @Override
    public Set<DomainVariable> getSetOfDomainVariables() {
        Set<DomainVariable> result = leftSide.getSetOfDomainVariables();
        result.addAll(rightSide.getSetOfDomainVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getSetOfPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getSetOfPropositionalVariables() {
        Set<PropositionalVariable> result = leftSide
                .getSetOfPropositionalVariables();
        result.addAll(rightSide.getSetOfPropositionalVariables());
        return result;
    }

}
