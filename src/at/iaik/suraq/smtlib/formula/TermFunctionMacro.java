/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.InvalidParametersException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TermFunctionMacro extends FunctionMacro {

    /**
     * The body of this macro.
     */
    private Term body;

    /**
     * Constructs a new <code>TermFunctionMacro</code> with the given values.
     * 
     * @param name
     *            the name of this macro.
     * @param a
     *            list of parameters
     * @param paramMap
     *            the map from parameters to types.
     * @param body
     *            the actual body.
     * @throws InvalidParametersException
     *             if the size of the parameter list and the type map do not
     *             match.
     */
    public TermFunctionMacro(Token name, List<Token> parameters,
            Map<Token, SExpression> paramMap, Term body)
            throws InvalidParametersException {
        super(name, parameters, paramMap);
        this.body = body;
    }

    /**
     * Constructs a new <code>PropositionalFunctionMacro</code>, which is a deep
     * copy of the given one
     * 
     * @param macro
     *            the macro to (deep) copy.
     */
    public TermFunctionMacro(TermFunctionMacro macro) {
        super(macro);
        this.body = macro.body.deepTermCopy();
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof TermFunctionMacro))
            return false;
        TermFunctionMacro other = (TermFunctionMacro) obj;
        return other.name.equals(name) && other.parameters.equals(parameters)
                && other.paramMap.equals(paramMap) && other.body.equals(body);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return name.hashCode() ^ parameters.hashCode() ^ paramMap.hashCode()
                ^ body.hashCode();
    }

    /**
     * Returns the function body of this macro.
     * 
     * @return the <code>body</code>
     */
    public Term getBody() {
        return body;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.FunctionMacro#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        body.removeArrayEqualities();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.FunctionMacro#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        body.arrayPropertiesToFiniteConjunctions(indexSet);
    }

    /**
     * Returns the type of the term of this macro's body.
     * 
     * @return the type of the term of this macro's body.
     */
    @Override
    public SExpression getType() {
        return body.getType();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.EqualityFormula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    public Set<Formula> removeArrayWrites(Formula topLevelFormula,
            Set<Token> noDependenceVars) {
        Set<Formula> constraints = new HashSet<Formula>();
        body.removeArrayWrites(topLevelFormula, constraints, noDependenceVars);
        return constraints;
    }

    /**
     * Replaces array-read expressions with uninterpreted function instances
     */
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        body.arrayReadsToUninterpretedFunctions(noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        return body.getUninterpretedFunctions();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.FunctionMacro#getBodyExpression()
     */
    @Override
    public SExpression getBodyExpression() {
        return body.toSmtlibV2();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        body.substituteUninterpretedFunction(oldFunction, newFunction);
    }

    /**
     * @param topLevelFormula
     * @param noDependenceVars
     * @return
     */
    public Set<Formula> makeArrayReadsSimple(Formula topLevelFormula,
            Set<Token> noDependenceVars) {
        Set<Formula> constraints = new HashSet<Formula>();
        body.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
        return constraints;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*public TermFunctionMacro uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {

        Term newBody = body.uninterpretedPredicatesToAuxiliaryVariables(
                topLeveFormula, constraints, noDependenceVars);
        try {
            return new TermFunctionMacro(name, parameters, paramMap, newBody);
        } catch (InvalidParametersException exc) {
            throw new RuntimeException(
                    "Unexpectedly unable to create TermFunctionMacro.", exc);
        }

    }*/

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getAssertPartition() {
        return body.getPartitionsFromSymbols();
    }
    
    

    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    public void uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
    	
		        body.uninterpretedPredicatesToAuxiliaryVariables(
		                 topLeveFormula, predicateInstances, instanceParameters, noDependenceVars);
    }
    
    
    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    public void uninterpretedFunctionsToAuxiliaryVariables(
            Formula topLeveFormula, Map<String,List<DomainVariable>> functionInstances, 
            Map<DomainVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
		
		       body.uninterpretedFunctionsToAuxiliaryVariables(
		                topLeveFormula, functionInstances, instanceParameters, noDependenceVars);
    }
}
