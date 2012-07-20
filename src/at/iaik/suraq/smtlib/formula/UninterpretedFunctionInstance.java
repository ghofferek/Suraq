/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.exceptions.WrongFunctionTypeException;
import at.iaik.suraq.exceptions.WrongNumberOfParametersException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.util.Util;

/**
 * An instance of an uninterpreted function.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class UninterpretedFunctionInstance extends DomainTerm {

    public static boolean method = true; // TODO remove this

    /**
     * 
     */
    private static final long serialVersionUID = -2770188384661175641L;

    /**
     * The function of which this is an instance.
     */
    private UninterpretedFunction function;

    /**
     * The list of parameters of this instance.
     */
    private final List<DomainTerm> parameters;

    public UninterpretedFunctionInstance(UninterpretedFunction function,
            List<DomainTerm> parameters, int partition)
            throws WrongNumberOfParametersException, WrongFunctionTypeException {
        this(function, parameters);
        if (partition != -1) {
            assert (partition == this.assertPartition || this.assertPartition == -1);
            this.assertPartition = partition;
            this.assertPartition = partition;
        }
    }

    /**
     * Constructs a new <code>UninterpretedFunctionInstance</code> with the
     * given values.
     * 
     * @param function
     *            the function that is applied.
     * @param parameters
     *            the parameters of the function
     * 
     * @throws WrongNumberOfParametersException
     *             if the number of parameters of the function does not match
     *             the size of <code>parameters</code>.
     * @throws WrongFunctionTypeException
     *             if the type of the given function is not <code>Value</code>.
     */
    public UninterpretedFunctionInstance(UninterpretedFunction function,
            List<DomainTerm> parameters)
            throws WrongNumberOfParametersException, WrongFunctionTypeException {
        if (function.getNumParams() != parameters.size())
            throw new WrongNumberOfParametersException();
        this.function = function;
        if (!function.getType().equals(SExpressionConstants.VALUE_TYPE))
            throw new WrongFunctionTypeException(
                    "Expected a domain function. Received type: "
                            + function.getType().toString());
        this.parameters = new ArrayList<DomainTerm>(parameters);

        Set<Integer> partitions = new HashSet<Integer>();
        for (DomainTerm parameter : this.parameters)
            partitions.addAll(parameter.getPartitionsFromSymbols());
        assert (partitions.size() <= 2);
        if (partitions.size() == 2)
            partitions.remove(-1);
        assert (partitions.size() == 1);
        this.assertPartition = partitions.iterator().next();
    }

    /**
     * Constructs a new <code>UninterpretedFunctionInstance</code> with just one
     * parameter.
     * 
     * @param function
     *            the function that is applied
     * @param term
     *            the single parameter of the function.
     * @throws WrongNumberOfParametersException
     *             if the number of parameters of the function does not match
     *             the size of <code>parameters</code>.
     */
    public UninterpretedFunctionInstance(UninterpretedFunction function,
            DomainTerm term) throws WrongNumberOfParametersException {
        if (function.getNumParams() != 1)
            throw new WrongNumberOfParametersException();
        this.function = function;
        List<DomainTerm> params = new ArrayList<DomainTerm>();
        params.add(term);
        this.parameters = params;
    }

    /**
     * Returns the function of which this is an instance
     * 
     * @return the <code>function</code>
     */
    public UninterpretedFunction getFunction() {
        return function;
    }

    /**
     * Returns a copy of the list of parameters of this instance.
     * 
     * @return the <code>parameters</code> (copy)
     */
    public List<DomainTerm> getParameters() {
        return new ArrayList<DomainTerm>(parameters);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#isEvar(java.util.Collection)
     */
    @Override
    public boolean isEvar(Collection<DomainVariable> uVars) {
        for (DomainTerm term : parameters) {
            if (!term.isEvar(uVars))
                return false;
        }
        return true;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public UninterpretedFunctionInstance deepTermCopy() {
        List<DomainTerm> parameters = new ArrayList<DomainTerm>();
        for (DomainTerm term : this.parameters)
            parameters.add(term.deepTermCopy());
        try {
            return new UninterpretedFunctionInstance(new UninterpretedFunction(
                    function), parameters, assertPartition);
        } catch (SuraqException exc) {
            // This should never happen!
            assert (false);
            throw new RuntimeException(
                    "Unexpected situation while copying uninterpreted function instance.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> variables = new HashSet<ArrayVariable>();
        for (Term term : parameters)
            variables.addAll(term.getArrayVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> variables = new HashSet<DomainVariable>();
        for (Term term : parameters)
            variables.addAll(term.getDomainVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> variables = new HashSet<PropositionalVariable>();
        for (Term term : parameters)
            variables.addAll(term.getPropositionalVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = new HashSet<String>();
        for (Term term : parameters)
            result.addAll(term.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = new HashSet<FunctionMacro>();
        for (Term term : parameters)
            result.addAll(term.getFunctionMacros());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = new HashSet<String>();
        result.add(function.getName().toString());
        for (Term term : parameters)
            result.addAll(term.getUninterpretedFunctionNames());
        return result;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof UninterpretedFunctionInstance))
            return false;
        UninterpretedFunctionInstance other = (UninterpretedFunctionInstance) obj;
        if (!other.parameters.equals(parameters))
            return false;
        if (!other.function.equals(function))
            return false;
        return true;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return function.hashCode() ^ parameters.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> result = new HashSet<DomainTerm>();
        for (DomainTerm term : parameters) {
            result.addAll(term.getIndexSet());
        }
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteTerm(Map)
     */
    @Override
    public Term substituteTerm(Map<Token, ? extends Term> paramMap) {
        List<DomainTerm> convertedParameters = new ArrayList<DomainTerm>();
        for (int count = 0; count < parameters.size(); count++)
            convertedParameters.add((DomainTerm) parameters.get(count)
                    .substituteTerm(paramMap));

        UninterpretedFunctionInstance result;
        try {
            result = new UninterpretedFunctionInstance(function,
                    convertedParameters);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected error while subsituting parameters.", exc);
        }
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        List<SExpression> expr = new ArrayList<SExpression>();
        expr.add(function.getName());
        for (DomainTerm term : parameters)
            expr.add(term.toSmtlibV2());
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        for (Term param : parameters)
            param.arrayPropertiesToFiniteConjunctions(indexSet);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        for (Term param : parameters)
            param.removeArrayEqualities();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        for (Term param : parameters)
            param.removeArrayWrites(topLevelFormula, constraints,
                    noDependenceVars);

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        for (DomainTerm term : parameters)
            if (term instanceof ArrayRead) {
                int index = parameters.indexOf(term);
                parameters.set(index, ((ArrayRead) term)
                        .toUninterpretedFunctionInstance(noDependenceVars));
            } else
                term.arrayReadsToUninterpretedFunctions(noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        Set<UninterpretedFunction> result = new HashSet<UninterpretedFunction>();
        if(method)
            result.add(function);
        for (Term term : parameters)
            result.addAll(term.getUninterpretedFunctions());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        if (function.getName().equals(oldFunction)) {
            function = newFunction;
            assert (newFunction.getType()
                    .equals(SExpressionConstants.VALUE_TYPE));
        }
        for (Term term : parameters)
            term.substituteUninterpretedFunction(oldFunction, newFunction);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public UninterpretedFunctionInstance flatten() {
        List<DomainTerm> flattenedParams = new ArrayList<DomainTerm>();
        for (DomainTerm term : parameters)
            flattenedParams.add((DomainTerm) term.flatten());
        try {
            return new UninterpretedFunctionInstance(function, flattenedParams);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected error while flattening UninterpretedFunctionInstance.",
                    exc);
        }

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public void makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        for (Term param : parameters)
            param.makeArrayReadsSimple(topLevelFormula, constraints,
                    noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*@Override
    public DomainTerm uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {

        List<DomainTerm> newParameters = new ArrayList<DomainTerm>();
        for (DomainTerm term : parameters)
            newParameters.add(term.uninterpretedPredicatesToAuxiliaryVariables(
                    topLeveFormula, constraints, noDependenceVars));

        UninterpretedFunctionInstance result;
        try {
            result = new UninterpretedFunctionInstance(function, newParameters);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected error while converting predicates to auxiliary variables.",
                    exc);
        }

        return result;
    }*/

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = function.getAssertPartitionFromSymbols();

        for (DomainTerm term : parameters)
            partitions.addAll(term.getPartitionsFromSymbols());

        return partitions;
    }
    
    
    
    
    
    
    /**
     * Searches function-instance and instance-parameter mappings for match of 
     * current UninterpretedFunctionInstance's function and parameter valuation.
     * 
      * @param functionInstances
     *            map containing mapping from function names to auxiliary variables.
     *               
     * @param instanceParameters
     *            map containing mapping from auxiliary variables to function instance 
     *            parameters.  
     *                                       
     * @return the found auxiliary DomainVariable. If no match exists NULL is returned.
     */
    private DomainVariable matchFunctionInstance(Map<String,List<DomainVariable>> functionInstances, 
            Map<DomainVariable,List<DomainTerm>> instanceParameters) {
    
    	String functionName = function.getName().toString();
    	List<DomainVariable> instances = functionInstances.get(functionName);
    	
    	if(instances!=null)
	    	for (DomainVariable instance : instances){
	    		List<DomainTerm> instParameters = instanceParameters.get(instance);
	    		
	    		boolean found=true;
	    		
	    		
	    		for (int x=0; x < instParameters.size(); x++){
	    			DomainTerm a = parameters.get(x);
	    			DomainTerm b = instParameters.get(x);
	    		    
	    			if(!(a.equals(b))){
		    			found=false;
	    				break;
	    			}
	    		}
	    		
	    		if(found)
	    			return instance;
	    	}
    	
    	return null;
    }
    
    /**
     * Add the current UninterpretedFunctionInstance as new entry into the function-instance
     * and instance-parameter mappings.
     * 
      * @param functionInstances
     *            map containing mapping from function names to auxiliary variables.
     *               
     * @param instanceParameters
     *            map containing mapping from auxiliary variables to function instance 
     *            parameters.  
     *                                       
     * @return newly created auxiliary DomainVariable as substitute for the current UninterpretedFunctionInstace.
     */
    private DomainVariable addFunctionInstance(Formula topLeveFormula, Map<String,List<DomainVariable>> functionInstances, 
            Map<DomainVariable,List<DomainTerm>> instanceParameters) {
    	
    	DomainVariable result = null;
    				
		Set<String> instancesStr = new HashSet<String>();
		for (DomainVariable dv : instanceParameters.keySet())
			  instancesStr.add(dv.getVarName());
		  
    	String varName = Util.freshVarName(topLeveFormula,function.getName().toString(),instancesStr);
    	result = new DomainVariable(varName);
       
    	String functionName = function.getName().toString();
    	List<DomainVariable> instances = functionInstances.get(functionName);
    	if(instances==null)
    		instances = new ArrayList<DomainVariable>();	
    	instances.add(result);
    	functionInstances.put(functionName, instances);
    	
    	instanceParameters.put(result, parameters);
    	
    	return result;
    }
 
    
    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    public void uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters,  Set<Token> noDependenceVars) {  	
    	return; //functions are not allowed to have predicates as parameters.
    }
    
    
    /**
     * @see at.iaik.suraq.formula.DomainTerm#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public void uninterpretedFunctionsToAuxiliaryVariables(
            Formula topLeveFormula, Map<String,List<DomainVariable>> functionInstances, 
            Map<DomainVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
    	  throw new RuntimeException(
                  "uninterpretedFunctionsToAuxiliaryVariables cannot be called on an UninterpretedFunctionInstance.\nUse applyReplaceUninterpretedFunctions instead.");
    }
    
    
    /**
     * Performs a substitution of UninterpretedFunctionInstances with auxiliary DomainVariables.
     *
     * @param topLeveFormula
     *            the top level formula (for finding fresh variable names). 
     * 
     * @param functionInstances
     *            map containing mapping from function names to auxiliary variables.
     *               
     * @param instanceParameters
     *            map containing mapping from auxiliary variables to function instance 
     *            parameters.  
     *                                       
     * @return auxiliary DomainVariable as substitute for the current UninterpretedFunctionInstace.
     */
    public DomainVariable applyReplaceUninterpretedFunctions(
            Formula topLeveFormula, Map<String,List<DomainVariable>> functionInstances, 
            Map<DomainVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
            // TODO: optimize!!!
		    	List<DomainTerm> newParameters = new ArrayList<DomainTerm>(parameters); 
		    	
		    	for (DomainTerm term : newParameters) {
		            if (term instanceof UninterpretedFunctionInstance) {
		            	
		            	 DomainVariable auxiliaryVariable =  ((UninterpretedFunctionInstance) term)
		            			 .applyReplaceUninterpretedFunctions(topLeveFormula,
		            					 	functionInstances, instanceParameters, noDependenceVars);
		            	 
		            	 
		            	 // added by chille 03.07.2012
		            	 parameters.set(parameters.indexOf(term), auxiliaryVariable); 
		            	 
		            	 // removed by chille 03.07.2012
		            	 // parameters.remove(term);
		            	 // parameters.add(auxiliaryVariable);
		
		            } else {
		                term.uninterpretedFunctionsToAuxiliaryVariables(topLeveFormula,functionInstances, instanceParameters, noDependenceVars);
		            }
		        }
		    	
		        DomainVariable result = matchFunctionInstance(functionInstances, instanceParameters);
		        
		        if(result==null)
		        {
		        	result = addFunctionInstance(topLeveFormula, functionInstances, instanceParameters);
		        	//System.out.print('*');
    		        // Check if the function is noDependence or at least one parameter of the function is noDependence
    		        // This might be conservative and might not be complete (i.e., may
    		        // result unnecessary unrealizability)
    		        
		        }
		        else
		        {
		            //System.out.print('_');
		        }
		        	
		        	
	        	
		        boolean insert = false;
		        
		        
		        for (DomainTerm term : parameters) {
		        	if (Util.termContainsAny(term, noDependenceVars))  {	
		        		insert=true;	
		        		break; //exit immediately.
		        	}
		        }
		      
		        String funcName = function.getName().toString();
		        for (Token t : noDependenceVars) {
		        	if(funcName.equals(t.toString())){
		        		insert = true;
		        		break;
		        	}
		        }
		        
		        if (insert==true)
		        {
		            // chillebold 2012-07-09
		            // this is called several times per noDependenceVar, but it does not matter,
		            // because it is added to a Set 
		            // http://docs.oracle.com/javase/1.4.2/docs/api/java/util/Set.html#add%28java.lang.Object%29
		        	noDependenceVars.add(new Token(result.getVarName()));
		        	//System.out.print('+');
		        }
		        return result;
    }            

}
