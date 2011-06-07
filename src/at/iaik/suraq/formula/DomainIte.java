/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Collection;
import java.util.Set;

/**
 * An if-then-else-style domain term.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class DomainIte extends DomainTerm {

    /**
     * The condition.
     */
    private final Formula condition;

    /**
     * The then-branch.
     */
    private final DomainTerm thenBranch;

    /**
     * The else-branch
     */
    private final DomainTerm elseBranch;

    /**
     * 
     * Constructs a new <code>DomainIte</code>.
     * 
     * @param condition
     *            the condition
     * @param thenBranch
     *            the value of the then-branch
     * @param elseBranch
     *            the value of the else-branch
     */
    public DomainIte(Formula condition, DomainTerm thenBranch,
            DomainTerm elseBranch) {
        this.condition = condition;
        this.thenBranch = thenBranch;
        this.elseBranch = elseBranch;
    }

    /**
     * @see at.iaik.suraq.formula.DomainTerm#isEvar(java.util.Collection)
     */
    @Override
    public boolean isEvar(Collection<DomainVariable> uVars) {
        // not applicable to DomainIte
        return false;
    }

    /**
     * Returns the condition.
     * 
     * @return the <code>condition</code>
     */
    public Formula getCondition() {
        return condition;
    }

    /**
     * Returns the then branch.
     * 
     * @return the <code>thenBranch</code>
     */
    public DomainTerm getThenBranch() {
        return thenBranch;
    }

    /**
     * Returns the else branch.
     * 
     * @return the <code>elseBranch</code>
     */
    public DomainTerm getElseBranch() {
        return elseBranch;
    }

    /**
     * @see at.iaik.suraq.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return new DomainIte(condition.deepFormulaCopy(),
                (DomainTerm) thenBranch.deepTermCopy(),
                (DomainTerm) elseBranch.deepTermCopy());
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
