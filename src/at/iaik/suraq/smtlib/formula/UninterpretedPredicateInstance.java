/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
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
import at.iaik.suraq.util.DebugHelper;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.ImmutableArrayList;
import at.iaik.suraq.util.Util;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class UninterpretedPredicateInstance extends PropositionalTerm {

    /**
     * 
     */
    private static final long serialVersionUID = 7300557099748461681L;

    /**
     * The function of which this is an instance.
     */
    private final UninterpretedFunction function;

    /**
     * The list of parameters of this instance.
     */
    private final ImmutableArrayList<DomainTerm> parameters;

    private UninterpretedPredicateInstance(UninterpretedFunction function,
            List<DomainTerm> parameters, int partition)
            throws WrongNumberOfParametersException, WrongFunctionTypeException {
        this(function, parameters);
        if (partition != -1) {
            assert (partition == this.assertPartition || this.assertPartition == -1);
            this.assertPartition = partition;
        }
    }

    public static UninterpretedPredicateInstance create(
            UninterpretedFunction function, List<DomainTerm> parameters,
            int partition) throws WrongNumberOfParametersException,
            WrongFunctionTypeException {
        return (UninterpretedPredicateInstance) FormulaCache.term
                .put(new UninterpretedPredicateInstance(function, parameters,
                        partition));
    }

    /**
     * Constructs a new <code>UninterpretedPredicateInstance</code> with the
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
    private UninterpretedPredicateInstance(UninterpretedFunction function,
            List<DomainTerm> parameters)
            throws WrongNumberOfParametersException, WrongFunctionTypeException {
        if (function.getNumParams() != parameters.size())
            throw new WrongNumberOfParametersException();
        this.function = function;
        if (!function.getType().equals(SExpressionConstants.BOOL_TYPE))
            throw new WrongFunctionTypeException(
                    "Expected a domain function. Received type: "
                            + function.getType().toString());
        this.parameters = new ImmutableArrayList<DomainTerm>(parameters);

        Set<Integer> partitions = new HashSet<Integer>();
        for (DomainTerm parameter : this.parameters)
            partitions.addAll(parameter.getPartitionsFromSymbols());
        assert (partitions.size() <= 2);
        if (partitions.size() == 2)
            partitions.remove(-1);
        assert (partitions.size() == 1);
        this.assertPartition = partitions.iterator().next();
    }
    
    public static UninterpretedPredicateInstance create(
            UninterpretedFunction function, List<DomainTerm> parameters)
            throws WrongNumberOfParametersException, WrongFunctionTypeException {
        return (UninterpretedPredicateInstance) FormulaCache.term
                .put(new UninterpretedPredicateInstance(function, parameters));
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof UninterpretedPredicateInstance))
            return false;
        if (this.hashCode() != obj.hashCode())
            return false;
        UninterpretedPredicateInstance other = (UninterpretedPredicateInstance) obj;
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
        return function.hashCode() * 31 + parameters.hashCode();
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
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public UninterpretedPredicateInstance deepFormulaCopy() {
        return this; // experimental
        /*
        List<DomainTerm> parameterCopies = new ArrayList<DomainTerm>();
        for (DomainTerm term : parameters)
            parameterCopies.add(term.deepTermCopy());
        try {
            return new UninterpretedPredicateInstance(
                    new UninterpretedFunction(function), parameterCopies,
                    assertPartition);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected situation whily copying predicate.", exc);
        }
        */
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
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = new HashSet<String>();
        DebugHelper.predicates.add(function.getName());
        if(method)
            result.add(function.getName().toString());
        for (Term term : parameters)
            result.addAll(term.getUninterpretedFunctionNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = new HashSet<String>();
        for (Term term : parameters)
            result.addAll(term.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = new HashSet<FunctionMacro>();
        for (Term term : parameters)
            result.addAll(term.getFunctionMacros());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
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
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        return deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, ? extends Term> paramMap) {
        List<DomainTerm> convertedParameters = new ArrayList<DomainTerm>();
        for (int count = 0; count < parameters.size(); count++)
            convertedParameters.add((DomainTerm) parameters.get(count)
                    .substituteTerm(paramMap));

        UninterpretedPredicateInstance result;
        try {
            result = new UninterpretedPredicateInstance(function,
                    convertedParameters);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected error while subsituting parameters.", exc);
        }
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(at.iaik.suraq.sexp.Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Formula substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        UninterpretedFunction function = this.function;
        
        if (function.getName().equals(oldFunction)) {
            function = newFunction;
            assert (newFunction.getType()
                    .equals(SExpressionConstants.BOOL_TYPE));
        }

        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term term : parameters)
            paramNew.add((DomainTerm)term.substituteUninterpretedFunctionTerm(oldFunction, newFunction));
        
        try {
            return new UninterpretedPredicateInstance(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }
    @Override
    public Term substituteUninterpretedFunctionTerm(Token oldFunction,
            UninterpretedFunction newFunction) {
        UninterpretedFunction function = this.function;
        
        if (function.getName().equals(oldFunction)) {
            function = newFunction;
            assert (newFunction.getType()
                    .equals(SExpressionConstants.BOOL_TYPE));
        }

        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term term : parameters)
            paramNew.add((DomainTerm)term.substituteUninterpretedFunctionTerm(oldFunction, newFunction));
        
        try {
            return new UninterpretedPredicateInstance(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }
    


    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualities()
     */
    @Override
    public Formula removeArrayEqualities() {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm)param.removeArrayEqualitiesTerm());
        
        try {
            return new UninterpretedPredicateInstance(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }
    @Override
    public Term removeArrayEqualitiesTerm() {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm)param.removeArrayEqualitiesTerm());
        
        try {
            return new UninterpretedPredicateInstance(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm)param.arrayPropertiesToFiniteConjunctionsTerm(indexSet));
        
        try {
            return new UninterpretedPredicateInstance(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }
    @Override
    public Term arrayPropertiesToFiniteConjunctionsTerm(Set<DomainTerm> indexSet) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm)param.arrayPropertiesToFiniteConjunctionsTerm(indexSet));
        
        try {
            return new UninterpretedPredicateInstance(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        return deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public UninterpretedPredicateInstance flatten() {
        List<DomainTerm> flattenedParams = new ArrayList<DomainTerm>();
        for (DomainTerm term : parameters)
            flattenedParams.add((DomainTerm) term.flatten());
        try {
            return new UninterpretedPredicateInstance(function, flattenedParams);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected error while flattening UninterpretedFunctionInstance.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
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
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm) param.removeArrayWritesTerm(
                    topLevelFormula, constraints, noDependenceVars));

        try {
            return new UninterpretedPredicateInstance(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }
    @Override
    public Term removeArrayWritesTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm) param.removeArrayWritesTerm(
                    topLevelFormula, constraints, noDependenceVars));

        try {
            return new UninterpretedPredicateInstance(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions(java.util.Set)
     */
    @Override
    public Formula arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (DomainTerm term : parameters)
            if (term instanceof ArrayRead) {
                paramNew.add(((ArrayRead) term)
                        .toUninterpretedFunctionInstance(noDependenceVars));
            } else
                paramNew.add((DomainTerm)term.arrayReadsToUninterpretedFunctionsTerm(noDependenceVars));
        
        try {
            return new UninterpretedPredicateInstance(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }
    @Override
    public Term arrayReadsToUninterpretedFunctionsTerm(Set<Token> noDependenceVars) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (DomainTerm term : parameters)
            if (term instanceof ArrayRead) {
                paramNew.add(((ArrayRead) term)
                        .toUninterpretedFunctionInstance(noDependenceVars));
            } else
                paramNew.add((DomainTerm)term.arrayReadsToUninterpretedFunctionsTerm(noDependenceVars));
        
        try {
            return new UninterpretedPredicateInstance(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }
    
    public static boolean method = true; // TODO remove this

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        Set<UninterpretedFunction> result = new HashSet<UninterpretedFunction>();
        if(method) // TODO: remove IF
            result.add(function);
        for (Term term : parameters)
            result.addAll(term.getUninterpretedFunctions());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {

        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm) param.makeArrayReadsSimpleTerm(
                    topLevelFormula, constraints, noDependenceVars));

        try {
            return new UninterpretedPredicateInstance(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }
    @Override
    public Term makeArrayReadsSimpleTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {

        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm) param.makeArrayReadsSimpleTerm(
                    topLevelFormula, constraints, noDependenceVars));

        try {
            return new UninterpretedPredicateInstance(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*@Override
    public PropositionalTerm uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        PropositionalVariable newVar = new PropositionalVariable(
                Util.freshVarName(topLeveFormula, "aux"));
        List<PropositionalTerm> terms = new ArrayList<PropositionalTerm>();
        terms.add(newVar);
        terms.add(FormulaTerm.create(this.deepFormulaCopy()));
        constraints.add(new PropositionalEq(terms, true));

        if (Util.formulaContainsAny(this, noDependenceVars))
            noDependenceVars.add(new Token(newVar.getVarName()));

        return newVar;
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
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm()
     */
    @Override
    public OrFormula transformToConsequentsForm() {
        return (OrFormula) transformToConsequentsForm(false, true);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm(boolean,
     *      boolean)
     */
    @Override
    public Formula transformToConsequentsForm(boolean notFlag,
            boolean firstLevel) {

        if (firstLevel == true) {
            List<Formula> literals = new ArrayList<Formula>();
            literals.add(this);
            return OrFormula.generate(literals);
        }
        if (notFlag == true)
            return NotFormula.create(this);

        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteTerm(Map)
     */
    @Override
    public Term substituteTerm(Map<Token, ? extends Term> paramMap) {
        return (Term) substituteFormula(paramMap);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.List,
     *      java.util.Map)
     */
    @Override
    public PropositionalVariable tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding) {

        assert (clauses != null);
        assert (encoding != null);

        Set<Integer> partitions = this.getPartitionsFromSymbols();
        assert (partitions.size() == 1 || partitions.size() == 2);
        if (partitions.size() == 2)
            partitions.remove(-1);
        assert (partitions.size() == 1);
        int partition = partitions.iterator().next();
        PropositionalVariable tseitinVar = Util.freshTseitinVar(partition);
        encoding.put(tseitinVar, this.deepFormulaCopy());

        List<Formula> disjuncts = new ArrayList<Formula>(2);
        disjuncts.add(NotFormula.create(tseitinVar));
        disjuncts.add(this.deepFormulaCopy());
        clauses.add(OrFormula.generate(disjuncts));

        disjuncts.clear();
        disjuncts.add(tseitinVar);
        disjuncts.add(NotFormula.create(this.deepFormulaCopy()));
        clauses.add(OrFormula.generate(disjuncts));

        return tseitinVar;
    }
    
    /**
     * Searches predicate-instance and instance-parameter mappings for match of 
     * current UninterpretedPredicateInstance's function and parameter valuation.
     * 
      * @param predicateInstances
     *            map containing mapping from function names to auxiliary variables.
     *               
     * @param instanceParameters
     *            map containing mapping from auxiliary variables to function instance 
     *            parameters.  
     *                                       
     * @return the found auxiliary PropositionalVariable. If no match exists NULL is returned.
     */
    private PropositionalVariable matchPredicateInstance(Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters) {
    
    	String predicateName = function.getName().toString();
    	List<PropositionalVariable> instances = predicateInstances.get(predicateName);
    	
    	if(instances!=null)
	    	for (PropositionalVariable instance : instances){
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
     * Add the current UninterpretedPredicateInstance as new entry into the predicate-instance
     * and instance-parameter mappings.
     * 
      * @param predicateInstances
     *            map containing mapping from function names to auxiliary variables.
     *               
     * @param instanceParameters
     *            map containing mapping from auxiliary variables to function instance 
     *            parameters.  
     *                                       
     * @return newly created auxiliary DomainVariable as substitute for the current UninterpretedFunctionInstace.
     */
    private PropositionalVariable addPredicateInstance(Formula topLeveFormula, Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters) {
    	
    	PropositionalVariable result = null;
    	
		Set<String> instancesStr = new HashSet<String>();
		for (PropositionalVariable pv : instanceParameters.keySet())
			  instancesStr.add(pv.getVarName());
		
    	String varName = Util.freshVarNameCached(topLeveFormula,function.getName().toString(),instancesStr);
    	
    	result = PropositionalVariable.create(varName);
       
    	String predicateName = function.getName().toString();
    	List<PropositionalVariable> instances = predicateInstances.get(predicateName);
    	if(instances==null)
    		instances = new ArrayList<PropositionalVariable>();	
    	instances.add(result);
    	predicateInstances.put(predicateName, instances);
    	
    	instanceParameters.put(result, parameters);
    	
    	return result;
    }
    

    
    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Formula uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters,  Set<Token> noDependenceVars) {
    	
    	  throw new RuntimeException(
                  "uninterpretedPredicatesToAuxiliaryVariables cannot be called on an UninterpretedPredicateInstance.\nUse applyReplaceUninterpretedPredicates instead.");
    }
    @Override
    public Term uninterpretedPredicatesToAuxiliaryVariablesTerm(
            Formula topLeveFormula, Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters,  Set<Token> noDependenceVars) {
        
          throw new RuntimeException(
                  "uninterpretedPredicatesToAuxiliaryVariables cannot be called on an UninterpretedPredicateInstance.\nUse applyReplaceUninterpretedPredicates instead.");
    }
    
    
    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Formula uninterpretedFunctionsToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();

        for (DomainTerm term : parameters) {
            if (term instanceof UninterpretedFunctionInstance) {
                DomainVariable auxiliaryVariable = ((UninterpretedFunctionInstance) term)
                        .applyReplaceUninterpretedFunctions(topLeveFormula,
                                functionInstances, instanceParameters,
                                noDependenceVars);

                // chillebold: imho: the order of these terms may be important!
                // parameters.remove(term);
                // parameters.add(auxiliaryVariable);

                // verify if still working - need a testcase for this
                // Let's try this instead.
                // I don't know how the for-loop is implemented.
                // In some programming languages the following action throws an
                // exception, because the for-loop does not know how to
                // continue.
                //parameters.set(parameters.indexOf(term), auxiliaryVariable);
                paramNew.add(auxiliaryVariable);
                

            } else
                paramNew.add((DomainTerm)term.uninterpretedFunctionsToAuxiliaryVariablesTerm(topLeveFormula,
                        functionInstances, instanceParameters, noDependenceVars));
        }

        try {
            return new UninterpretedPredicateInstance(function, paramNew);
        } catch (SuraqException e) {
            System.err.println("is: "+function.getNumParams() + " should:" + paramNew.size());
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }
    @Override
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();

        for (DomainTerm term : parameters) {
            if (term instanceof UninterpretedFunctionInstance) {
                DomainVariable auxiliaryVariable = ((UninterpretedFunctionInstance) term)
                        .applyReplaceUninterpretedFunctions(topLeveFormula,
                                functionInstances, instanceParameters,
                                noDependenceVars);

                // chillebold: imho: the order of these terms may be important!
                // parameters.remove(term);
                // parameters.add(auxiliaryVariable);

                // verify if still working - need a testcase for this
                // Let's try this instead.
                // I don't know how the for-loop is implemented.
                // In some programming languages the following action throws an
                // exception, because the for-loop does not know how to
                // continue.
                //parameters.set(parameters.indexOf(term), auxiliaryVariable);
                paramNew.add(auxiliaryVariable);
                

            } else
                term.uninterpretedFunctionsToAuxiliaryVariablesTerm(topLeveFormula,
                        functionInstances, instanceParameters, noDependenceVars);
        }

        try {
            return new UninterpretedPredicateInstance(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * Performs a substitution of UninterpretedPredicateInstances with auxiliary PropositionalVariables.
     *
     * @param topLeveFormula
     *            the top level formula (for finding fresh variable names). 
     * 
     * @param predicateInstances
     *            map containing mapping from predicate names to auxiliary variables.
     *               
     * @param instanceParameters
     *            map containing mapping from auxiliary variables to function instance 
     *            parameters.  
     *                                       
     * @return auxiliary PropositionalVariable as substitute for the current UninterpretedPredicateInstace.
     */
	public PropositionalVariable applyReplaceUninterpretedPredicates(Formula topLeveFormula,
			Map<String, List<PropositionalVariable>> predicateInstances,
			Map<PropositionalVariable, List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
	
	        PropositionalVariable result = matchPredicateInstance(predicateInstances,instanceParameters);
	        
	        if(result==null)
	        	result = addPredicateInstance(topLeveFormula, predicateInstances, instanceParameters);
	        
	        
	        // Check if the function is noDependence or at least one parameter of the function is noDependence
	        // This might be conservative and might not be complete (i.e., may
	        // result unnecessary unrealizability)		
	        
	        boolean insert = false;
	        for (DomainTerm term : parameters) {
	        	if (Util.termContainsAny(term, noDependenceVars))  
	        		insert=true;		        				    		        		
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
	        	noDependenceVars.add(Token.generate(result.getVarName())); 
	        }
	        return result;		
	}
    

    @Override
    public Formula replaceEquivalences(Formula topLeveFormula, Map<EqualityFormula, String> replacements, Set<Token> noDependenceVars)
    {
        throw new RuntimeException(
                "replaceEquivalences cannot be called on an UninterpretedFunctions.\n"
                        + "UninterpretedFunctions should be removed by now.");
    }

    @Override
    public Formula removeDomainITE(Formula topLevelFormula, Set<Token> noDependenceVars, List<Formula> andPreList)
    {
        throw new RuntimeException(
                "removeDomainITE cannot be called on an UninterpretedFunctions.\n"
                        + "UninterpretedFunctions should be removed by now.");
    }
	
}
