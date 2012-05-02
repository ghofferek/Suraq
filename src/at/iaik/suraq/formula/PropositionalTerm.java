/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.List;
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
     * The assert-partitions
     */
	protected List<Integer> assertPartitions = new ArrayList<Integer>();
	
    /**
     * @see at.iaik.suraq.formula.Term#getType()
     */
    @Override
    public SExpression getType() {
        return SExpressionConstants.BOOL_TYPE;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        // Nothing to do here.
        // No array equalities contained here.
        return;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        // Nothing to do
        return this;
    }

    @Override
    public abstract PropositionalTerm flatten();

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public abstract PropositionalTerm uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars);

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    public List<Integer> getAssertPartition(){
    	return new ArrayList<Integer>(this.assertPartitions);
    }
}
