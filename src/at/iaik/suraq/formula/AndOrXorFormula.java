/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * A common superclass for And- Or- and Xor-formulas to avoid code redundancy.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class AndOrXorFormula extends BooleanCombinationFormula {
    /**
     * The list of sub-formulas.
     */
    protected final List<Formula> formulas;

    /**
     * 
     * Constructs a new <code>AndOrXorFormula</code>. Initializes the list of
     * subformulas.
     * 
     * @param formulas
     *            the list of subformulas.
     */
    protected AndOrXorFormula(Collection<? extends Formula> formulas) {
        this.formulas = new ArrayList<Formula>();
        this.formulas.addAll(formulas);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getSetOfArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getSetOfArrayVariables() {
        Set<ArrayVariable> variables = new HashSet<ArrayVariable>();
        for (Formula formula : formulas)
            variables.addAll(formula.getSetOfArrayVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getSetOfDomainVariables()
     */
    @Override
    public Set<DomainVariable> getSetOfDomainVariables() {
        Set<DomainVariable> variables = new HashSet<DomainVariable>();
        for (Formula formula : formulas)
            variables.addAll(formula.getSetOfDomainVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getSetOfPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getSetOfPropositionalVariables() {
        Set<PropositionalVariable> variables = new HashSet<PropositionalVariable>();
        for (Formula formula : formulas)
            variables.addAll(formula.getSetOfPropositionalVariables());
        return variables;
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
        return new XorFormula(subformulas);
    }
}
