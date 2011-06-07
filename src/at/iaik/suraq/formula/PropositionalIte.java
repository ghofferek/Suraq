/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

/**
 * Represents an if-then-else-style formula.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalIte extends BooleanCombinationFormula {

    /**
     * The formula that represents the condition.
     */
    private final Formula condition;

    /**
     * The formula that represents the then-branch.
     */
    private final Formula thenBranch;

    /**
     * The formula that represents the else-branch.
     */
    private final Formula elseBranch;

    /**
     * 
     * Constructs a new <code>PropositionalIte</code>.
     * 
     * @param condition
     *            the formula that represents the condition
     * @param thenBranch
     *            the formula that represents the then-branch
     * @param elseBranch
     *            the formula that represents the else-branch
     */
    public PropositionalIte(Formula condition, Formula thenBranch,
            Formula elseBranch) {
        this.condition = condition;
        this.thenBranch = thenBranch;
        this.elseBranch = elseBranch;
    }

    /**
     * @see at.iaik.suraq.formula.BooleanCombinationFormula#getSubFormulas()
     */
    @Override
    public Collection<Formula> getSubFormulas() {
        List<Formula> list = new ArrayList<Formula>();
        list.add(condition);
        list.add(thenBranch);
        list.add(elseBranch);
        return list;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return new PropositionalIte(condition.deepFormulaCopy(),
                thenBranch.deepFormulaCopy(), elseBranch.deepFormulaCopy());
    }

    /**
     * @see at.iaik.suraq.formula.Term#getSetOfArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getSetOfArrayVariables() {
        Set<ArrayVariable> result = thenBranch.getSetOfArrayVariables();
        result.addAll(elseBranch.getSetOfArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getSetOfDomainVariables()
     */
    @Override
    public Set<DomainVariable> getSetOfDomainVariables() {
        Set<DomainVariable> result = thenBranch.getSetOfDomainVariables();
        result.addAll(elseBranch.getSetOfDomainVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getSetOfPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getSetOfPropositionalVariables() {
        Set<PropositionalVariable> result = thenBranch
                .getSetOfPropositionalVariables();
        result.addAll(elseBranch.getSetOfPropositionalVariables());
        return result;
    }
}
