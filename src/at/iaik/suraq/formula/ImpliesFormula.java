/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;

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

    /**
     * @see at.iaik.suraq.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        List<Formula> list = new ArrayList<Formula>();
        list.add((new NotFormula(leftSide)).negationNormalForm());
        list.add(rightSide.negationNormalForm());
        return new OrFormula(list);
    }

    /**
     * @return the <code>leftSide</code>
     */
    public Formula getLeftSide() {
        return leftSide;
    }

    /**
     * @return the <code>rightSide</code>
     */
    public Formula getRightSide() {
        return rightSide;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = leftSide.getUninterpretedFunctionNames();
        result.addAll(rightSide.getUninterpretedFunctionNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = leftSide.getFunctionMacroNames();
        result.addAll(rightSide.getFunctionMacroNames());
        return result;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof ImpliesFormula))
            return false;
        return ((ImpliesFormula) obj).leftSide.equals(leftSide)
                && ((ImpliesFormula) obj).rightSide.equals(rightSide);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return leftSide.hashCode() ^ rightSide.hashCode();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> result = leftSide.getIndexSet();
        result.addAll(rightSide.getIndexSet());
        return result;
    }

}
