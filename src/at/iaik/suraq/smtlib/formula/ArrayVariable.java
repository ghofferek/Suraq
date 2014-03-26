/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.IOException;
import java.io.Serializable;
import java.io.Writer;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;

/**
 * A class representing an array variable.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayVariable extends ArrayTerm implements Serializable {
    /**
     * 
     */
    private static final long serialVersionUID = 4046182524846284758L;
    /**
     * The name of the variable.
     */
    private final String varName;

    private final int hashCode;

    public static ArrayVariable create(String varName) {
        return (ArrayVariable) FormulaCache.term
                .put(new ArrayVariable(varName));
    }

    public static ArrayVariable create(Token name) {
        return (ArrayVariable) FormulaCache.term.put(new ArrayVariable(name
                .toString()));
    }

    public static ArrayVariable create(String varName, int assertPartition) {
        return (ArrayVariable) FormulaCache.term.put(new ArrayVariable(varName,
                assertPartition));
    }

    public static ArrayVariable create(Token name, int assertPartition) {
        return (ArrayVariable) FormulaCache.term.put(new ArrayVariable(name
                .toString(), assertPartition));
    }

    /**
     * 
     * Constructs a new <code>ArrayVariable</code>.
     * 
     * @param varName
     *            the name of the variable.
     */
    private ArrayVariable(String varName) {
        this.varName = varName;
        hashCode = varName.hashCode();
    }

    /**
     * 
     * Constructs a new <code>ArrayVariable</code>.
     * 
     * @param name
     *            the <code>String</code> representing the variable name.
     * @param assertPartition
     *            the assert-partition of the variable
     */
    private ArrayVariable(String name, int assertPartition) {
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
        if (!(obj instanceof ArrayVariable))
            return false;
        if (this.hashCode != ((ArrayVariable) obj).hashCode)
            return false;

        return varName.equals(((ArrayVariable) obj).varName);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return hashCode;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return this; // experimental
        // return new ArrayVariable(new String(varName), this.assertPartition);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public void getArrayVariables(Set<ArrayVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        result.add(ArrayVariable.create(varName));
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getDomainVariables()
     */
    @Override
    public void getDomainVariables(Set<DomainVariable> result,
            Set<SMTLibObject> done) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getPropositionalVariables()
     */
    @Override
    public void getPropositionalVariables(Set<PropositionalVariable> result,
            Set<SMTLibObject> done) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacroNames()
     */
    @Override
    public void getFunctionMacroNames(Set<String> result, Set<SMTLibObject> done) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacros()
     */
    @Override
    public void getFunctionMacros(Set<FunctionMacro> result,
            Set<SMTLibObject> done) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done) {
        return;
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
    public Term substituteTerm(Map<Token, ? extends Term> paramMap,
            Map<SMTLibObject, SMTLibObject> done) {
        if (done.containsKey(this)) {
            assert (done.get(this) != null);
            assert (done.get(this) instanceof Term);
            return (Term) done.get(this);
        }
        Term result;
        if (paramMap.containsKey(Token.generate(varName)))
            result = paramMap.get(Token.generate(varName));
        else
            result = this;
        assert (result != null);
        done.put(this, result);
        return result;
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
    public Term arrayReadsToUninterpretedFunctionsTerm(
            Set<Token> noDependenceVars) {
        // nothing to do
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#uninterpretedFunctionsBackToArrayReads(java.util.Set,
     *      java.util.Map)
     */
    @Override
    public SMTLibObject uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars, Map<SMTLibObject, SMTLibObject> done) {
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Term substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions,
            Map<SMTLibObject, SMTLibObject> done) {
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#flatten()
     */
    @Override
    public Term flatten() {
        return ArrayVariable.create(varName);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, Set)
     */
    @Override
    public Term makeArrayReadsSimpleTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.ArrayTerm#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*
     * @Override public ArrayTerm uninterpretedPredicatesToAuxiliaryVariables(
     * Formula topLeveFormula, Set<Formula> constraints, Set<Token>
     * noDependenceVars) { return new ArrayVariable(varName); }
     */

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
     * @see at.iaik.suraq.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Term uninterpretedPredicatesToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        throw new RuntimeException(
                "uninterpretedPredicatesToAuxiliaryVariables cannot be called on an ArrayVariable.");

        // return;
    }

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        throw new RuntimeException(
                "uninterpretedFunctionsToAuxiliaryVariables cannot be called on an ArrayVariable.");

        // return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.ArrayTerm#removeDomainITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.List)
     */
    @Override
    public ArrayTerm removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Collection)
     */
    @Override
    public ArrayVariable removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints) {
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#writeTo(java.io.Writer)
     */
    @Override
    public void writeTo(Writer writer) throws IOException {
        writer.write(varName);
    }

}
