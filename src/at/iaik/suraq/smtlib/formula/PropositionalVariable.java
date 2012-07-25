/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.Serializable;
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
public class PropositionalVariable extends PropositionalTerm implements
        Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = 3473923317666080631L;
    /**
     * The name of the variable.
     */
    private final String varName;

    private final int hashCode;

    /**
     * 
     * Constructs a new <code>PropositionalVariable</code>.
     * 
     * @param varName
     *            the name of the variable.
     */
    public PropositionalVariable(String varName) {
        this.varName = varName;
        hashCode = varName.hashCode();
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
        hashCode = varName.hashCode();
    }

    /**
     * 
     * Constructs a new <code>PropositionalVariable</code>.
     * 
     * @param name
     *            the <code>Token</code> representing the variable name.
     * @param assertPartition
     *            the assert partition of the variable.
     */
    public PropositionalVariable(Token name, int assertPartition) {
        this.varName = name.toString();
        this.assertPartition = assertPartition;
        hashCode = varName.hashCode();
    }

    /**
     * 
     * Constructs a new <code>PropositionalVariable</code>.
     * 
     * @param name
     *            the <code>String</code> representing the variable name.
     * @param assertPartition
     *            the assert partition of the variable.
     */
    public PropositionalVariable(String name, int assertPartition) {
        this.varName = name.toString();
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
        if (!(obj instanceof PropositionalVariable))
            return false;
        if (this.hashCode != ((PropositionalVariable) obj).hashCode)
            return false;
        return varName.equals(((PropositionalVariable) obj).varName);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return hashCode;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return new PropositionalVariable(new String(varName),
                this.assertPartition);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return new PropositionalVariable(new String(varName),
                this.assertPartition);
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
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, ? extends Term> paramMap) {
        if (paramMap.containsKey(Token.generate(varName)))
            return (PropositionalTerm) paramMap.get(Token.generate(varName));
        else
            return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        // Nothing to do here.
        return this;
    }
    @Override
    public Term arrayPropertiesToFiniteConjunctionsTerm(Set<DomainTerm> indexSet) {
        // Nothing to do here.
        return this;
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
        return Token.generate(varName);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        // nothing to do
        return this;
    }

    @Override
    public Term removeArrayWritesTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        // nothing to do
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Formula arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        // nothing to do
        return this;
    }
    @Override
    public Term arrayReadsToUninterpretedFunctionsTerm(Set<Token> noDependenceVars) {
        // nothing to do
        return this;
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
    public Formula substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        return this;
    }
    @Override
    public Term substituteUninterpretedFunctionTerm(Token oldFunction,
            UninterpretedFunction newFunction) {
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        return this;
    }
    @Override
    public Term makeArrayReadsSimpleTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.PropositionalTerm#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*@Override
    public PropositionalTerm uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        return new PropositionalVariable(varName);
    }*/

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = new TreeSet<Integer>();
        partitions.add(this.assertPartition);
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
            return new NotFormula(this);

        return this;

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.Map)
     */
    @Override
    public PropositionalVariable tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding) {
        return new PropositionalVariable(varName, assertPartition);
    }
    

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    public Formula uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
    	return this;
    }
    public Term uninterpretedPredicatesToAuxiliaryVariablesTerm(
            Formula topLeveFormula, Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
        return this;
    }

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Formula uninterpretedFunctionsToAuxiliaryVariables(
            Formula topLeveFormula, Map<String,List<DomainVariable>> functionInstances, 
            Map<DomainVariable, List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
        return this;
    }
    @Override
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula, Map<String,List<DomainVariable>> functionInstances, 
            Map<DomainVariable, List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
        return this;
    }

    @Override
    public Formula replaceEquivalences(Formula topLeveFormula, Map<EqualityFormula, String> replacements, Set<Token> noDependenceVars)
    {
        return this;
    }
    

    @Override
    public Formula removeDomainITE(Formula topLevelFormula, Set<Token> noDependenceVars, List<Formula> andPreList)
    {
        return this;
    }
}
