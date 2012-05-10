/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * A class for formulas of the form (a => b).
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ImpliesFormula extends BooleanCombinationFormula {

    /**
     * The left side of the implication.
     */
    private Formula leftSide;

    /**
     * The right side of the implication.
     */
    private Formula rightSide;

    /**
     * 
     * Constructs a new <code>ImpliesFormula</code>.
     * 
     * @param leftSide
     *            the left side of the implication
     * @param rightSide
     *            the right side of the implication
     */
    public ImpliesFormula(Formula leftSide, Formula rightSide) {
        this.leftSide = leftSide;
        this.rightSide = rightSide;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.BooleanCombinationFormula#getSubFormulas()
     */
    @Override
    public Collection<Formula> getSubFormulas() {
        List<Formula> list = new ArrayList<Formula>();
        list.add(leftSide);
        list.add(rightSide);
        return list;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return new ImpliesFormula(leftSide.deepFormulaCopy(),
                rightSide.deepFormulaCopy());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> result = leftSide.getArrayVariables();
        result.addAll(rightSide.getArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> result = leftSide.getDomainVariables();
        result.addAll(rightSide.getDomainVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> result = leftSide
                .getPropositionalVariables();
        result.addAll(rightSide.getPropositionalVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        List<Formula> list = new ArrayList<Formula>();
        list.add((new NotFormula(leftSide)).negationNormalForm());
        list.add(rightSide.negationNormalForm());
        return new OrFormula(list);
    }

    /**
     * @return the <code>leftSide</code>
     */
    public Formula getLeftSide() {
        return leftSide;
    }

    /**
     * @return the <code>rightSide</code>
     */
    public Formula getRightSide() {
        return rightSide;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = leftSide.getUninterpretedFunctionNames();
        result.addAll(rightSide.getUninterpretedFunctionNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = leftSide.getFunctionMacroNames();
        result.addAll(rightSide.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = leftSide.getFunctionMacros();
        result.addAll(rightSide.getFunctionMacros());
        return result;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof ImpliesFormula))
            return false;
        return ((ImpliesFormula) obj).leftSide.equals(leftSide)
                && ((ImpliesFormula) obj).rightSide.equals(rightSide);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return leftSide.hashCode() ^ rightSide.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> result = leftSide.getIndexSet();
        result.addAll(rightSide.getIndexSet());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(java.util.Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, Term> paramMap) {
        return new ImpliesFormula(leftSide.substituteFormula(paramMap),
                rightSide.substituteFormula(paramMap));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        if (leftSide instanceof ArrayEq)
            leftSide = ((ArrayEq) leftSide).toArrayProperties();
        else
            leftSide.removeArrayEqualities();

        if (rightSide instanceof ArrayEq)
            rightSide = ((ArrayEq) rightSide).toArrayProperties();
        else
            rightSide.removeArrayEqualities();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        if (leftSide instanceof ArrayProperty)
            leftSide = ((ArrayProperty) leftSide).toFiniteConjunction(indexSet);
        else
            leftSide.arrayPropertiesToFiniteConjunctions(indexSet);

        if (rightSide instanceof ArrayProperty)
            rightSide = ((ArrayProperty) rightSide)
                    .toFiniteConjunction(indexSet);
        else
            rightSide.arrayPropertiesToFiniteConjunctions(indexSet);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        leftSide = leftSide.simplify();
        rightSide = rightSide.simplify();

        if (leftSide instanceof PropositionalConstant) {
            if (((PropositionalConstant) leftSide).getValue())
                return rightSide;
            else
                return new PropositionalConstant(true);
        }

        if (rightSide instanceof PropositionalConstant) {
            if (((PropositionalConstant) rightSide).getValue())
                return new PropositionalConstant(true);
            else
                return new NotFormula(leftSide).simplify();
        }

        if (leftSide.equals(rightSide))
            return new PropositionalConstant(true);

        if (leftSide instanceof NotFormula)
            if (rightSide.equals(((NotFormula) leftSide).getNegatedFormula()))
                return rightSide;

        if (rightSide instanceof NotFormula)
            if (leftSide.equals(((NotFormula) rightSide).getNegatedFormula()))
                return rightSide;

        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        return new ImpliesFormula(leftSide.flatten(), rightSide.flatten());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        return new SExpression(SExpressionConstants.IMPLIES,
                leftSide.toSmtlibV2(), rightSide.toSmtlibV2());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        leftSide.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);
        rightSide.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        leftSide.arrayReadsToUninterpretedFunctions(noDependenceVars);
        rightSide.arrayReadsToUninterpretedFunctions(noDependenceVars);

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        Set<UninterpretedFunction> result = leftSide
                .getUninterpretedFunctions();
        result.addAll(rightSide.getUninterpretedFunctions());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        leftSide.substituteUninterpretedFunction(oldFunction, newFunction);
        rightSide.substituteUninterpretedFunction(oldFunction, newFunction);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public void makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        leftSide.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
        rightSide.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        return new ImpliesFormula(
                leftSide.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars),
                rightSide.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars));
    }

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getAssertPartition() {
        Set<Integer> partitions = this.leftSide.getAssertPartition();
        partitions.addAll(this.rightSide.getAssertPartition());

        return partitions;
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

		// a => b equals NOT a OR b
		
		assert(notFlag == false);		

		List<Formula> subFormulas = new ArrayList<Formula>();		
		
		//left side
    	if (isValidChild(this.leftSide)) {
    		if (this.leftSide instanceof OrFormula){
    			ArrayList<Formula> disjuncts = (ArrayList<Formula>) ((OrFormula) this.leftSide).getDisjuncts();
    			for (Formula disjunct : disjuncts){
            		    				
    				Formula transformedSubFormula = disjunct.transformToConsequentsForm(!notFlag, false);    				
    				if (isAtom(disjunct))
    					transformedSubFormula = new NotFormula(transformedSubFormula);    				
    				subFormulas.add(transformedSubFormula);    				    			         				
    			}
    		}
    		else {
				Formula transformedSubFormula = this.leftSide.transformToConsequentsForm(!notFlag, false);    				
				if (isAtom(this.leftSide))
					transformedSubFormula = new NotFormula(transformedSubFormula);    				
				subFormulas.add(transformedSubFormula);        			
    		}
    	}
    	else
			throw new RuntimeException(
                    "Unexpected Chid: Child of an OR Formula can either be an OR Formula, a NOT Formula or an atom");		
		
		//right side	
    	if (isValidChild(this.rightSide)) {
    		if (this.rightSide instanceof OrFormula){
    			ArrayList<Formula> disjuncts = (ArrayList<Formula>) ((OrFormula) this.rightSide).getDisjuncts();
    			for (Formula disjunct : disjuncts){
            		Formula transformedSubFormula = disjunct.transformToConsequentsForm(notFlag, false);
            		subFormulas.add(transformedSubFormula);         				
    			}
    		}
    		else {
        		Formula transformedSubFormula = this.rightSide.transformToConsequentsForm(notFlag, false);
        		subFormulas.add(transformedSubFormula);        			
    		}
    	}
    	else
			throw new RuntimeException(
                    "Unexpected Chid: Child of an OR Formula can either be an OR Formula, a NOT Formula or an atom");		
		    	
        return new OrFormula(subFormulas);
	}     
	
    /** 
     * Checks if a given Formula is an atom or a NOT formula or a OR formula.
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

