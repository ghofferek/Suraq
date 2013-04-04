/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.Serializable;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * 
 * This class represents domain terms. A domain term is either a domain
 * variable, (a domain constant,) an array read expression, or a function call.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class DomainTerm extends Term implements Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = -328749262145943504L;

    /**
     * Checks whether this term consists of evars (with respect to the given
     * list of uvars) only.
     * 
     * @param uVars
     *            a collection of uvars.
     * @return <code>true</code> if this term consists of evars only,
     *         <code>false</code> otherwise.
     */
    public abstract boolean isEvar(Collection<DomainVariable> uVars);

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getType()
     */
    @Override
    public SExpression getType() {
        return SExpressionConstants.VALUE_TYPE;
    }

    /**
     * Returns a deep copy of this term.
     * 
     * @return a deep copy of this term.
     */
    @Override
    public abstract DomainTerm deepTermCopy();

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(t)
     */
    @Override
    public abstract Term uninterpretedPredicatesToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars);

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public abstract Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars);

    @Override
    public abstract DomainTerm uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars);

}
