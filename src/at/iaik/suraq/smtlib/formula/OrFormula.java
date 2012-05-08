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
 * A formula that is a disjunction of other formulas.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class OrFormula extends AndOrXorFormula {

    /**
     * 
     * Constructs a new <code>OrFormula</code>, consisting of the disjunction of
     * the given formulas.
     * 
     * @param formulas
     *            the formulas to disjunct.
     */
    public OrFormula(Collection<Formula> formulas) {
        super(formulas);
    }

    /**
     * Returns a collection of the disjuncted formulas.
     * 
     * @return a collection of the disjuncted formulas. (Copy)
     */
    public Collection<Formula> getDisjuncts() {
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
                if (((PropositionalConstant) formula).getValue()) {
                    return new PropositionalConstant(true);
                } else
                    formulas.remove(formula);
            }

            if (formula instanceof NotFormula) {
                if (((NotFormula) formula).isNegatedConstant() != null) {
                    if (!((NotFormula) formula).isNegatedConstant().getValue())
                        return new PropositionalConstant(true);
                }
                PropositionalVariable var = ((NotFormula) formula)
                        .isNegatedVariable();

                if (var != null) {
                    if (positiveVars.contains(var))
                        return new PropositionalConstant(true);
                    negativeVars.add(var);
                }

                if (formulas.contains(((NotFormula) formula)
                        .getNegatedFormula()))
                    return new PropositionalConstant(true);
            }

            if (formula instanceof PropositionalVariable) {
                if (negativeVars.contains(formula))
                    return new PropositionalConstant(true);
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
        return SExpressionConstants.OR;
    }
    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformFormulaToConsequentsFormula(at.iaik.suraq.smtlib.formula.Formula)
     */
	@Override
	public Formula transformToConsequentsForm(Formula formula) {
		return transformToConsequentsForm(formula, false, true);
	}
	
	 /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformFormulaToConsequentsFormula(at.iaik.suraq.smtlib.formula.Formula, boolean, boolean)
     */	
	@Override	
	public Formula transformToConsequentsForm(Formula formula, boolean notFlag, boolean firstLevel) { 
			    	
		List<Formula> subFormulas = new ArrayList<Formula>();
        for (Formula subFormula : this.formulas){
        	if (isValidChild(subFormula)) {
        		Formula transformedSubFormula = subFormula.transformToConsequentsForm(formula, notFlag, false);
        		subFormulas.add(transformedSubFormula);
        	}
        	//TODO: verschachtelte oder auflösen
        	else
    			throw new RuntimeException(
                        "Unexpected Chid: Child of an OR Formula can either be an OR Formula, a NOT Formula or an atom");
        }
        	
        return new OrFormula(subFormulas);
	}        

    /** 
     * Checks if a given Formula is an atom or a NOT formula.
     * An atom is either a <code>EqualityFormula</code>, a <code>PropositionalVariable</code>
     * or a <code>UninterpretedPredicateInstance</code>.
     * 
     * @param formula
     * 		formula to check 
     * @return true, iff formula is valid
     *  	 
     */
	public boolean isValidChild(Formula formula){
		if (formula instanceof OrFormula)
			return true;
		if (formula instanceof NotFormula)
			return true;		
		if (formula instanceof EqualityFormula)  
            return true;
		if (formula instanceof PropositionalVariable)
            return true;		
		if (formula instanceof UninterpretedPredicateInstance)
            return true;		
		return false;
	}
}
