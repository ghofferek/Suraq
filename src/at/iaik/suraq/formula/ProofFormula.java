/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ProofFormula implements Formula {
	
    /**
     * The proof type.
     */
    private Token proofType;

    /**
     * The list of sub proofs.
     */
    private List<ProofFormula> subProofs;

    /**
     * the formula which is proved
     */
    private Formula proofFormula;
    
	 /**
     * The assert-partitions
     */
	protected List<Integer> assertPartitions = new ArrayList<Integer>();
	
    
    /**
     * 
     * Constructs a new <code>ProofFormula</code>.
     * 
     * @param proofType
     *            the type of the proof
     * @param subProofs
     *            the list of all subproofs 
     * @param proofFormula
     *            the formula which has to be proved
     */
    public ProofFormula(Token proofType, List<ProofFormula> subProofs,
    		Formula proofFormula) {
    	
        this.proofType = proofType;
        assert(subProofs!=null);
        this.subProofs = subProofs;
        this.proofFormula = proofFormula;
    }
    
    /**
     * Creates a new <code>ProofFormula</code> which is of the same type as
     * <code>this</code> object and has the given subProofs and proofFormula.
     * 
     * @param subProofs
     *            the subProofs
     * @param proofFormula
     *            the proofFormula            
     * @return a new <code>ProofFormula</code> with the same type as
     *         <code>this</code>.
     */
    protected ProofFormula create(List<Formula> subProofs, Formula proofFormula) {
    	
    	List<ProofFormula> newSubProofs = new ArrayList<ProofFormula>();
    	
    	for (Formula formula : subProofs){
    		if(formula instanceof ProofFormula)
    			newSubProofs.add((ProofFormula) formula);
    		else
    			throw new RuntimeException("tried to add non-ProofFormula as a subProof!");
    	}
    	
    	ProofFormula instance = new ProofFormula(new Token(this.proofType),newSubProofs,proofFormula);
        
    	return instance;
    }
    
    /**
     * Returns the type of the proof.
     * 
     * @return the <code>proofType</code>
     */
    public Token getProofType() {
        return this.proofType;
    }

    /**
     * Returns the list of sub proofs
     * 
     * @return the <code>thenBranch</code>
     */
    public List<ProofFormula> getSubProofs() {
        return this.subProofs;
    }

    /**
     * Returns the formula which has to be proved
     * 
     * @return the <code>proofFormula</code>
     */
    public Formula getProofFormula() {
        return this.proofFormula;
    }
    

	@Override		// TODO: <bk> check if it works
	public ProofFormula deepFormulaCopy() {
        List<ProofFormula> subformulas = new ArrayList<ProofFormula>();
        for (ProofFormula formula : this.subProofs)
            subformulas.add(formula.deepFormulaCopy());		
		
		return new ProofFormula(new Token(this.proofType),
				subformulas, this.proofFormula.deepFormulaCopy());
	}	
	
	@Override
	public Set<ArrayVariable> getArrayVariables() {
		Set<ArrayVariable> variables = new HashSet<ArrayVariable>();
		for (ProofFormula formula : this.subProofs)
            variables.addAll(formula.getArrayVariables());
		 
		variables.addAll(this.proofFormula.getArrayVariables());
        return variables;
	}

	@Override
	public Set<DomainVariable> getDomainVariables() {
		Set<DomainVariable> variables = new HashSet<DomainVariable>();
		for (ProofFormula formula : this.subProofs)
            variables.addAll(formula.getDomainVariables());
		 
		variables.addAll(this.proofFormula.getDomainVariables());
        return variables;
	}

	@Override
	public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> variables = new HashSet<PropositionalVariable>();
        for (ProofFormula formula : this.subProofs)
            variables.addAll(formula.getPropositionalVariables());
        
        variables.addAll(this.proofFormula.getPropositionalVariables()); 
        return variables;
	}

	@Override
	public Set<String> getUninterpretedFunctionNames() {
        Set<String> functionNames = new HashSet<String>();
        for (ProofFormula formula : this.subProofs)
            functionNames.addAll(formula.getUninterpretedFunctionNames());
        
        functionNames.addAll(this.proofFormula.getUninterpretedFunctionNames()); 
        return functionNames;
	}

	@Override
	public Set<String> getFunctionMacroNames() {
        Set<String> macroNames = new HashSet<String>();
        for (ProofFormula formula : this.subProofs)
            macroNames.addAll(formula.getFunctionMacroNames());
        
        macroNames.addAll(this.proofFormula.getFunctionMacroNames()); 
        return macroNames;
	}

	@Override
	public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> macros = new HashSet<FunctionMacro>();
        for (ProofFormula formula : this.subProofs)
            macros.addAll(formula.getFunctionMacros());
        
        macros.addAll(this.proofFormula.getFunctionMacros()); 
        return macros;
	}

	@Override
	public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> indexSet = new HashSet<DomainTerm>();
        for (ProofFormula formula : this.subProofs)
            indexSet.addAll(formula.getIndexSet());
        
        indexSet.addAll(this.proofFormula.getIndexSet()); 
        return indexSet;
	}

	@Override
	public Formula negationNormalForm() throws SuraqException {
        List<Formula> nnfFormulas = new ArrayList<Formula>();
        for (ProofFormula formula : this.subProofs)
            nnfFormulas.add(formula.negationNormalForm());
         
        return create(nnfFormulas,this.proofFormula.negationNormalForm());
	}

	@Override
	public Formula substituteFormula(Map<Token, Term> paramMap) {
        List<Formula> convertedFormulas = new ArrayList<Formula>();
        for (ProofFormula formula : this.subProofs)
            convertedFormulas.add(formula.substituteFormula(paramMap));

        return create(convertedFormulas,this.proofFormula.substituteFormula(paramMap));
	}

	@Override
	public void substituteUninterpretedFunction(Token oldFunction,
			UninterpretedFunction newFunction) {
		for (ProofFormula formula : this.subProofs)
            formula.substituteUninterpretedFunction(oldFunction, newFunction);
		
		this.proofFormula.substituteUninterpretedFunction(oldFunction, newFunction);
	}

	@Override
	public void removeArrayEqualities() {
		for (ProofFormula formula : this.subProofs)
            formula.removeArrayEqualities();
				
        if (this.proofFormula instanceof ArrayEq)
        	this.proofFormula =((ArrayEq) this.proofFormula).toArrayProperties();
        else
        	this.proofFormula.removeArrayEqualities();		
	}

	@Override
	public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {	
		for (ProofFormula formula : this.subProofs)
            formula.arrayPropertiesToFiniteConjunctions(indexSet);
				
        if (this.proofFormula instanceof ArrayProperty)
        	this.proofFormula =((ArrayProperty) this.proofFormula).toFiniteConjunction(indexSet);
        else
        	this.proofFormula.arrayPropertiesToFiniteConjunctions(indexSet);
	}

	@Override
	public Formula simplify() {
        // Default, unless a subclass has more clever method
        for (int count = 0; count < this.subProofs.size(); count++)
        	this.subProofs.set(count, (ProofFormula) this.subProofs.get(count).simplify());
       
        this.proofFormula=this.proofFormula.simplify();
        
        return this;
	}

	@Override
	public Formula flatten() {
        List<Formula> flattenedFormulas = new ArrayList<Formula>();
        for (ProofFormula formula : this.subProofs)
            flattenedFormulas.add(formula.flatten());

        return create(flattenedFormulas,this.proofFormula.flatten());
	}

	@Override
	public SExpression toSmtlibV2() {
        List<SExpression> children = new ArrayList<SExpression>();
        children.add(this.proofType);
        for (ProofFormula formula : this.subProofs)
            children.add(formula.toSmtlibV2());
        
        children.add(this.proofFormula.toSmtlibV2());
        return new SExpression(children);
	}

	@Override
	public void removeArrayWrites(Formula topLevelFormula,
			Set<Formula> constraints, Set<Token> noDependenceVars) {
		for (ProofFormula formula : this.subProofs)
            formula.removeArrayWrites(topLevelFormula, constraints,
                    noDependenceVars);
		
		this.proofFormula.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);
	}

	@Override
	public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
		for (ProofFormula formula : this.subProofs)
	            formula.arrayReadsToUninterpretedFunctions(noDependenceVars);
		
		this.proofFormula.arrayReadsToUninterpretedFunctions(noDependenceVars);	
	}

	@Override
	public Set<UninterpretedFunction> getUninterpretedFunctions() { 
		Set<UninterpretedFunction> functionNames = new HashSet<UninterpretedFunction>();
		for (ProofFormula formula : this.subProofs)
			functionNames.addAll(formula.getUninterpretedFunctions());
		
		functionNames.addAll(this.proofFormula.getUninterpretedFunctions());	
	    return functionNames;
	}

	@Override
	public void makeArrayReadsSimple(Formula topLevelFormula,
			Set<Formula> constraints, Set<Token> noDependenceVars) {
		for (ProofFormula formula : this.subProofs)
            formula.makeArrayReadsSimple(topLevelFormula, constraints,
                    noDependenceVars);
		
		this.proofFormula.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
	}

	@Override
	public Formula uninterpretedPredicatesToAuxiliaryVariables(
			Formula topLeveFormula, Set<Formula> constraints,
			Set<Token> noDependenceVars) {
		
	       List<Formula> newFormulas = new ArrayList<Formula>();
	       for (ProofFormula formula : this.subProofs)
	            newFormulas.add(formula
	                    .uninterpretedPredicatesToAuxiliaryVariables(
	                            topLeveFormula, constraints, noDependenceVars));

	       Formula newProofFormula = this.proofFormula.uninterpretedPredicatesToAuxiliaryVariables(
                   topLeveFormula, constraints, noDependenceVars);
	       
	       return this.create(newFormulas, newProofFormula);
	}
	
	  /**
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.toSmtlibV2().toString();
    }
  
    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    public List<Integer> getAssertPartition(){
    	List<Integer> partitions = proofFormula.getAssertPartition(); 
     
    	for (ProofFormula proof : subProofs)
        	partitions.addAll(proof.getAssertPartition());
        
    	return partitions;
    }
    
}
