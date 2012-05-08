/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * 
 * A formula that is a conjunction of other formulas.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class AndFormula extends AndOrXorFormula {

    /**
     * 
     * Constructs a new <code>AndFormula</code>, consisting of the conjunction
     * of the given formulas.
     * 
     * @param formulas
     *            the formulas to conjunct.
     */
    public AndFormula(Collection<Formula> formulas) {
        super(formulas);
    }

    /**
     * Returns a collection of the conjuncted formulas.
     * 
     * @return a collection of the conjuncted formulas. (Copy)
     */
    public Collection<Formula> getConjuncts() {
        return new ArrayList<Formula>(formulas);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        Set<PropositionalVariable> negativeVars = new HashSet<PropositionalVariable>();
        Set<PropositionalVariable> positiveVars = new HashSet<PropositionalVariable>();

        for (int count = 0; count < formulas.size(); count++) {
            Formula formula = formulas.get(count).simplify();
            formulas.set(count, formula);
            if (formula instanceof PropositionalConstant) {
                if (!((PropositionalConstant) formula).getValue()) {
                    return new PropositionalConstant(false);
                } else
                    formulas.remove(formula);
            }

            if (formula instanceof NotFormula) {
                if (((NotFormula) formula).isNegatedConstant() != null) {
                    if (((NotFormula) formula).isNegatedConstant().getValue())
                        return new PropositionalConstant(false);
                }
                PropositionalVariable var = ((NotFormula) formula)
                        .isNegatedVariable();

                if (var != null) {
                    if (positiveVars.contains(var))
                        return new PropositionalConstant(false);
                    negativeVars.add(var);
                }

                if (formulas.contains(((NotFormula) formula)
                        .getNegatedFormula()))
                    return new PropositionalConstant(false);
            }

            if (formula instanceof PropositionalVariable) {
                if (negativeVars.contains(formula))
                    return new PropositionalConstant(false);
                positiveVars.add((PropositionalVariable) formula);
            }
        }

        // No simplifications found
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.AndOrXorFormula#getOperator()
     */
    @Override
    protected Token getOperator() {
        return SExpressionConstants.AND;
    }
    
    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm()
     */
	@Override
	public Formula transformToConsequentsForm() {
		return transformToConsequentsForm(false, true);
	}
	
	 /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm(boolean, boolean)
     */	
	@Override	
	public Formula transformToConsequentsForm(boolean notFlag, boolean firstLevel) { 
		
		assert(notFlag);

		//apply deMorgan rule: NOT (a AND b) <=> NOT a OR NOT b	
        	
		List<Formula> subFormulas = new ArrayList<Formula>();
        for (Formula subFormula : this.formulas){
        	if (isValidChild(subFormula)) {
        		if (subFormula instanceof AndFormula){
        			ArrayList<Formula> conjuncts = (ArrayList<Formula>) ((AndFormula) subFormula).getConjuncts();
        			for (Formula conjunct : conjuncts){
                		Formula transformedSubFormula = conjunct.transformToConsequentsForm(!notFlag, false);
                		subFormulas.add(transformedSubFormula);           				
        			}
        		}
        		else {
        			Formula transformedSubFormula = subFormula.transformToConsequentsForm(!notFlag, false);
        			
        			if (isAtom(subFormula))
        				transformedSubFormula = new NotFormula(transformedSubFormula);
        			
            		subFormulas.add(transformedSubFormula);    			
        		}
        	}
        	else
    			throw new RuntimeException(
                        "Unexpected Chid: Child of an AND Formula can either be an AND Formula, a NOT Formula or an atom");	        		
        }
        
		Formula orFormula = new OrFormula(subFormulas);
        return orFormula;
	}        

    /** 
     * Checks if a given Formula is an atom, and AND Formula or a NOT formula.
     * An atom is either a <code>EqualityFormula</code>, a <code>PropositionalVariable</code>
     * or a <code>UninterpretedPredicateInstance</code>.
     * 
     * @param formula
     * 		formula to check 
     * @return true, iff formula is valid
     *  	 
     */
	public boolean isValidChild(Formula formula){
		if (formula instanceof AndFormula)
			return true;
		if (formula instanceof NotFormula)
			return true;		
		if (isAtom(formula))
			return true;
		return false;
	}
	
    /** 
     * Checks if a given Formula is an atom.
     * An atom is either a <code>EqualityFormula</code>, a <code>PropositionalVariable</code>
     * or a <code>UninterpretedPredicateInstance</code>.
     * 
     * @param formula
     * 		formula to check 
     * @return true, iff formula is valid
     *  	 
     */
	public boolean isAtom(Formula formula){
		if (formula instanceof EqualityFormula)
            return true;
		if (formula instanceof PropositionalVariable)
            return true;		
		if (formula instanceof UninterpretedPredicateInstance)
            return true;		
		return false;
	}

}
