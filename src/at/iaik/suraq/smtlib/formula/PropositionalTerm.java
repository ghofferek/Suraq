/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.Set;

import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * A propositional term. I.e., either a propositional constant or a
 * propositional variable, or a propositional if-then-else construct.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class PropositionalTerm extends Term implements Formula {


    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getType()
     */
    @Override
    public SExpression getType() {
        return SExpressionConstants.BOOL_TYPE;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        // Nothing to do here.
        // No array equalities contained here.
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        // Nothing to do
        return this;
    }

    @Override
    public abstract PropositionalTerm flatten();

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public abstract PropositionalTerm uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars);
}
