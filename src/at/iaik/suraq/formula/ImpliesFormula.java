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
     * @see at.iaik.suraq.formula.Formula#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> result = leftSide.getArrayVariables();
        result.addAll(rightSide.getArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> result = leftSide.getDomainVariables();
        result.addAll(rightSide.getDomainVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> result = leftSide
                .getPropositionalVariables();
        result.addAll(rightSide.getPropositionalVariables());
        return result;
    }

}
