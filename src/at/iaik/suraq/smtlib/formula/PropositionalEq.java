/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * A formula consisting of the (in)equality of propositional terms.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalEq extends EqualityFormula {
    /**
     * 
     * Constructs a new <code>PropositionalEq</code>.
     * 
     * @param terms
     *            the terms of the (in)equality.
     * @param equal
     *            <code>true</code> if an equality should be constructed,
     *            <code>false</code> for an inequality.
     * 
     */
    public PropositionalEq(Collection<PropositionalTerm> propTerms,
            boolean equal) {
        super(propTerms, equal);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        List<PropositionalTerm> terms = new ArrayList<PropositionalTerm>();
        for (Term term : this.terms) {
            terms.add((PropositionalTerm) term.deepTermCopy());
        }
        return new PropositionalEq(terms, equal);
    }
    
    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformFormulaToConsequentsFormula(at.iaik.suraq.smtlib.formula.Formula)
     */
	@Override
	public Formula transformToConsequentsForm(Formula formula) {
		return transformToConsequentsForm(formula, false, true);
	}
	
    /** 
     * Transform formulas to formula for consequents.
     * Formulas for consequents should have the following structure:
     *  		- each atom is either a positive equality of two terms, a propositional variable,
     *  			or an uninterpreted predicate
     *   		- each literal is either an atom or a negation of an atom
     *   		- formula is always an or formula which consists of at least one literal 
     *   
     * @param fomrula
     * 			to be transformed into a consequents formula 
     * @param notFlag
     * 			indicates if number of not operations occurred so far is even or odd 
     * 			(notFlag=true equates to odd number)
     * @param firstLevel
     * 			indicates if function call appeared in the first recursion step
     * @return the new transformed formula is possible, if not null
     *  	 
     */
	
	public Formula transformToConsequentsForm(Formula formula, boolean notFlag, boolean firstLevel) {
		
		if (terms.size()!=2)
			throw new RuntimeException(
					"Equality should have only two terms for consequents form");

		
		List<PropositionalTerm> terms = new ArrayList<PropositionalTerm>();
	    for (Term term : this.terms) {
	    	terms.add((PropositionalTerm) term.deepTermCopy());
	    	}
	    
	    Formula equalityFormula;
		if (this.equal==true)
			equalityFormula = new PropositionalEq(terms, true);		
		else
			equalityFormula = new NotFormula (new PropositionalEq(terms, true));		
		
		if (firstLevel==true){
			List<Formula> literals = new ArrayList<Formula>();			

			literals.add(equalityFormula);
			Formula orFormula = new OrFormula(literals);
			return	orFormula;	
		}
		return equalityFormula;
			
	}       
}
