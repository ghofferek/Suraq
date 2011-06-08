/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.exceptions.WrongNumberOfParametersException;

/**
 * An instance of an uninterpreted function.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class UninterpretedFunctionInstance extends DomainTerm {

    /**
     * The function of which this is an instance.
     */
    private final UninterpretedFunction function;

    /**
     * The list of parameters of this instance.
     */
    private final List<? extends DomainTerm> parameters;

    /**
     * Constructs a new <code>UninterpretedFunctionInstance</code> with the
     * given values.
     * 
     * @param function
     *            the function that is applied.
     * @param parameters
     *            the parameters of the function
     * 
     * @throws WrongNumberOfParametersException
     *             if the number of parameters of the function does not match
     *             the size of <code>parameters</code>.
     */
    public UninterpretedFunctionInstance(UninterpretedFunction function,
            List<DomainTerm> parameters)
            throws WrongNumberOfParametersException {
        if (function.getNumParams() != parameters.size())
            throw new WrongNumberOfParametersException();
        this.function = function;
        this.parameters = new ArrayList<DomainTerm>(parameters);
    }

    /**
     * Returns the function of which this is an instance
     * 
     * @return the <code>function</code>
     */
    public UninterpretedFunction getFunction() {
        return function;
    }

    /**
     * Returns a copy of the list of parameters of this instance.
     * 
     * @return the <code>parameters</code> (copy)
     */
    public List<DomainTerm> getParameters() {
        return new ArrayList<DomainTerm>(parameters);
    }

    /**
     * @see at.iaik.suraq.formula.DomainTerm#isEvar(java.util.Collection)
     */
    @Override
    public boolean isEvar(Collection<DomainVariable> uVars) {
        for (DomainTerm term : parameters) {
            if (!term.isEvar(uVars))
                return false;
        }
        return true;
    }

    /**
     * @see at.iaik.suraq.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        List<DomainTerm> parameters = new ArrayList<DomainTerm>();
        for (DomainTerm term : this.parameters)
            parameters.add((DomainTerm) term.deepTermCopy());
        try {
            return new UninterpretedFunctionInstance(new UninterpretedFunction(
                    function), parameters);
        } catch (WrongNumberOfParametersException exc) {
            // This should never happen!
            assert (false);
            throw new RuntimeException(
                    "Unexpected situation while copying uninterpreted function instance.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> variables = new HashSet<ArrayVariable>();
        for (Term term : parameters)
            variables.addAll(term.getArrayVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> variables = new HashSet<DomainVariable>();
        for (Term term : parameters)
            variables.addAll(term.getDomainVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> variables = new HashSet<PropositionalVariable>();
        for (Term term : parameters)
            variables.addAll(term.getPropositionalVariables());
        return variables;
    }
}
