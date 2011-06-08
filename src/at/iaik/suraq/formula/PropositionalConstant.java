/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.HashSet;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;

/**
 * A formula that consists of a simple propositional constant.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalConstant extends PropositionalTerm {

    private final boolean constant;

    /**
     * 
     * Constructs a new <code>PropositionalConstant</code>.
     * 
     * @param constant
     *            the value to use.
     */
    public PropositionalConstant(boolean constant) {
        this.constant = constant;
    }

    /**
     * Returns the value of this constant.
     * 
     * @return the value of this constant
     */
    public boolean getValue() {
        return constant;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return new PropositionalConstant(constant);
    }

    /**
     * @see at.iaik.suraq.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return new PropositionalConstant(constant);
    }

    /**
     * @see at.iaik.suraq.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        return new HashSet<ArrayVariable>();
    }

    /**
     * @see at.iaik.suraq.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        return new HashSet<DomainVariable>();
    }

    /**
     * @see at.iaik.suraq.formula.Term#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        return new HashSet<PropositionalVariable>();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        return new PropositionalConstant(constant);
    }

}
