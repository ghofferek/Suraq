/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import at.iaik.suraq.exceptions.WrongNumberOfParametersException;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class FunctionTerm extends DomainTerm {

    /**
     * The function.
     */
    private final UninterpretedFunction function;

    /**
     * The function parameters.
     */
    private final List<DomainTerm> parameters;

    /**
     * 
     * Constructs a new <code>FunctionTerm</code> with the given values.
     * 
     * @param function
     *            the function that is applied.
     * @param parameters
     *            the parameters of the function
     * @throws WrongNumberOfParametersException
     *             if the number of parameters of the function does not match
     *             the size of <code>parameters</code>.
     */
    public FunctionTerm(UninterpretedFunction function,
            List<? extends DomainTerm> parameters)
            throws WrongNumberOfParametersException {
        if (function.getNumParams() != parameters.size())
            throw new WrongNumberOfParametersException();
        this.function = function;
        this.parameters = new ArrayList<DomainTerm>(parameters);
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

}
