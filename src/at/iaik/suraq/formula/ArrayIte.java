/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Set;

/**
 * An if-then-else-style array term.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayIte extends ArrayTerm {

    /**
     * The condition.
     */
    private final Formula condition;

    /**
     * The then-branch.
     */
    private final ArrayTerm thenBranch;

    /**
     * The else-branch
     */
    private final ArrayTerm elseBranch;

    /**
     * 
     * Constructs a new <code>ArrayIte</code>.
     * 
     * @param condition
     *            the condition
     * @param thenBranch
     *            the value of the then-branch
     * @param elseBranch
     *            the value of the else-branch
     */
    public ArrayIte(Formula condition, ArrayTerm thenBranch,
            ArrayTerm elseBranch) {
        this.condition = condition;
        this.thenBranch = thenBranch;
        this.elseBranch = elseBranch;
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
    public ArrayTerm getThenBranch() {
        return thenBranch;
    }

    /**
     * Returns the else branch.
     * 
     * @return the <code>elseBranch</code>
     */
    public ArrayTerm getElseBranch() {
        return elseBranch;
    }

    /**
     * @see at.iaik.suraq.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return new ArrayIte(condition.deepFormulaCopy(),
                (ArrayTerm) thenBranch.deepTermCopy(),
                (ArrayTerm) elseBranch.deepTermCopy());
    }

    /**
     * @see at.iaik.suraq.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> result = thenBranch.getArrayVariables();
        result.addAll(elseBranch.getArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> result = thenBranch.getDomainVariables();
        result.addAll(elseBranch.getDomainVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> result = thenBranch
                .getPropositionalVariables();
        result.addAll(elseBranch.getPropositionalVariables());
        return result;
    }
}
