/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.Serializable;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.util.FormulaCache;

/**
 * A class representing domain variables.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class DomainVariable extends DomainTerm implements Serializable {

    /**
     * unique serial number
     */
    private static final long serialVersionUID = -2173510375009985016L;

    /**
     * The name of the variable.
     */
    private final String varName;

    private final int hashCode;

    
    public static DomainVariable create(String varName)
    {
        return FormulaCache.domainVarFormula.put(new DomainVariable(varName));
    }
    public static DomainVariable create(Token name)
    {
        return FormulaCache.domainVarFormula.put(new DomainVariable(name.toString()));
    }    
    public static DomainVariable create(String varName, int assertPartition)
    {
        return FormulaCache.domainVarFormula.put(new DomainVariable(varName, assertPartition));
    }   
    public static DomainVariable create(Token name, int assertPartition)
    {
        return FormulaCache.domainVarFormula.put(new DomainVariable(name.toString(), assertPartition));
    }
    
    /**
     * 
     * Constructs a new <code>DomainVariable</code>.
     * 
     * @param varName
     *            the name of the variable.
     */
    private DomainVariable(String varName) {
        this.varName = varName;
        hashCode = varName.hashCode();
    }


    /**
     * 
     * Constructs a new <code>DomainVariable</code>.
     * 
     * @param name
     *            the <code>String</code> representing the variable name.
     * @param assertPartition
     *            the assert partition of the <code>DomainVariable</code>.
     */
    private DomainVariable(String name, int assertPartition) {
        this.varName = name;
        this.assertPartition = assertPartition;
        hashCode = varName.hashCode();
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
        if (this == obj)
            return true;
        if (!(obj instanceof DomainVariable))
            return false;
        if (this.hashCode != ((DomainVariable) obj).hashCode)
            return false;
        return varName.equals(((DomainVariable) obj).varName);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return hashCode;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#isEvar(java.util.Collection)
     */
    @Override
    public boolean isEvar(Collection<DomainVariable> uVars) {
        return !uVars.contains(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public DomainTerm deepTermCopy() {
        return this; // experimental
        //return DomainVariable.create(new String(varName), this.assertPartition);
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
        Set<DomainVariable> result = new HashSet<DomainVariable>();
        result.add(DomainVariable.create(varName));
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        return new HashSet<PropositionalVariable>();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacroNames()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        return new HashSet<FunctionMacro>();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacros()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        return new HashSet<String>();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        return new HashSet<String>();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        return new HashSet<DomainTerm>();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteTerm(Map)
     */
    @Override
    public Term substituteTerm(Map<Token, ? extends Term> paramMap) {
        if (paramMap.containsKey(Token.generate(varName)))
            return paramMap.get(Token.generate(varName));
        else
            return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        return Token.generate(varName);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Term arrayPropertiesToFiniteConjunctionsTerm(Set<DomainTerm> indexSet) {
        // nothing to do here
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayEqualitiesTerm()
     */
    @Override
    public Term removeArrayEqualitiesTerm() {
        // nothing to do here
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Term removeArrayWritesTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        // nothing to do
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Term arrayReadsToUninterpretedFunctionsTerm(Set<Token> noDependenceVars) {
        // nothing to do
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        return new HashSet<UninterpretedFunction>();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Term substituteUninterpretedFunctionTerm(Token oldFunction,
            UninterpretedFunction newFunction) {
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#flatten()
     */
    @Override
    public Term flatten() {
        return this; // experimental
        //return DomainVariable.create(varName);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Term makeArrayReadsSimpleTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
   /* @Override
    public DomainTerm uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        return DomainVariable.create(varName);
    }*/

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = new TreeSet<Integer>();
        partitions.add(assertPartition);
        return partitions;
    }

    /**
     * @see at.iaik.suraq.formula.DomainTerm#uninterpretedPredicatesToAuxiliaryVariables()
     */
    @Override
    public Term uninterpretedPredicatesToAuxiliaryVariablesTerm(
            Formula topLeveFormula, Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {  	
    	return this;
    }

    
    /**
     * @see at.iaik.suraq.formula.DomainTerm#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula, Map<String,List<DomainVariable>> functionInstances, 
            Map<DomainVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
        return this;
    }
    
}
