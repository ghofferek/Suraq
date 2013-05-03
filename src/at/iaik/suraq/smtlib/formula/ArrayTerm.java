/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.Serializable;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * 
 * This class represents array terms. An array term is either an array variable,
 * or an array write expression.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class ArrayTerm extends Term implements Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = -6798333514399114160L;

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getType()
     */
    @Override
    public SExpression getType() {
        return SExpressionConstants.ARRAY_TYPE;
    }

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public abstract Term uninterpretedPredicatesToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars);

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public abstract Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars);

    @Override
    public abstract ArrayTerm uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars);

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeDomainITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.List)
     */
    @Override
    public abstract ArrayTerm removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList);
}
