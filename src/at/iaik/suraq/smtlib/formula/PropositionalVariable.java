/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * A class for formulas that consist just of one propositional variable.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalVariable extends PropositionalTerm {

    /**
     * The name of the variable.
     */
    private final String varName;

    /**
     * The assert-partitions
     */
    protected int assertPartition = Term.GLOBAL_PARTITION;

    /**
     * 
     * Constructs a new <code>PropositionalVariable</code>.
     * 
     * @param varName
     *            the name of the variable.
     */
    public PropositionalVariable(String varName) {
        this.varName = varName;
    }

    /**
     * 
     * Constructs a new <code>PropositionalVariable</code>.
     * 
     * @param name
     *            the <code>Token</code> representing the variable name.
     */
    public PropositionalVariable(Token name) {
        this.varName = name.toString();
    }

    /**
     * 
     * Constructs a new <code>PropositionalVariable</code>.
     * 
     * @param name
     *            the <code>Token</code> representing the variable name.
     * @param assertPartition
     * 			  the assert partition of the variable.           
     */    
    public PropositionalVariable(Token name, int assertPartition) {
        this.varName = name.toString();
    	this.assertPartition = assertPartition;        
    }    
    
    /**
     * 
     * Constructs a new <code>PropositionalVariable</code>.
     * 
     * @param name
     *            the <code>String</code> representing the variable name.
     * @param assertPartition
     * 			  the assert partition of the variable.           
     */    
    public PropositionalVariable(String name, int assertPartition) {
    	this.varName = name.toString();
    	this.assertPartition = assertPartition;
	}

	/**
     * Get the variable name.
     * 
     * @return the <code>varName</code>
     */
    public String getVarName() {
        return varName;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof PropositionalVariable))
            return false;
        return varName.equals(((PropositionalVariable) obj).varName);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return varName.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return new PropositionalVariable(new String(varName));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return new PropositionalVariable(new String(varName));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        return new HashSet<ArrayVariable>();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        return new HashSet<DomainVariable>();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> result = new HashSet<PropositionalVariable>();
        result.add(new PropositionalVariable(varName));
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        return this.deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        return new HashSet<String>();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        return new HashSet<String>();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        return new HashSet<FunctionMacro>();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        return new HashSet<DomainTerm>();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteTerm(java.util.Map)
     */
    @Override
    public Term substituteTerm(Map<Token, Term> paramMap) {
        if (paramMap.containsKey(new Token(varName)))
            return paramMap.get(new Token(varName));
        else
            return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(java.util.Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, Term> paramMap) {
        if (paramMap.containsKey(new Token(varName)))
            return (PropositionalTerm) paramMap.get(new Token(varName));
        else
            return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        // Nothing to do here.
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public PropositionalVariable flatten() {
        return new PropositionalVariable(varName);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        return new Token(varName);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        // nothing to do
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        // nothing to do
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        return new HashSet<UninterpretedFunction>();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public void makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.PropositionalTerm#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public PropositionalTerm uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        return new PropositionalVariable(varName);
    }
    
    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getAssertPartition() {
        Set<Integer> partitions = new TreeSet<Integer>();
        partitions.add(assertPartition);
        return partitions;
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
	
	@Override
    public Formula transformToConsequentsForm(Formula formula, boolean notFlag, boolean firstLevel) {
		
		PropositionalVariable probVar = new PropositionalVariable(new String(varName), assertPartition);
		Formula propVarFormula = new FormulaTerm (probVar);
		
		if (firstLevel==true){
			List<Formula> literals = new ArrayList<Formula>();			

			literals.add(propVarFormula);
			Formula orFormula = new OrFormula(literals);
			return	orFormula;	
		}
		return propVarFormula;
			
	}

}
