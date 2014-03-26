/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.Writer;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.HashTagContainer;
import at.iaik.suraq.util.Util;

/**
 * A formula that consists of a simple propositional constant.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalConstant extends PropositionalTerm {

    /**
     * 
     */
    private static final long serialVersionUID = 48734596062800807L;
    private final boolean constant;

    /**
     * 
     * Constructs a new <code>PropositionalConstant</code>.
     * 
     * @param constant
     *            the value to use.
     */
    private PropositionalConstant(boolean constant) {
        this.constant = constant;
    }

    public static PropositionalConstant create(boolean constant) {
        return FormulaCache.propConst.put(new PropositionalConstant(constant));
    }

    /**
     * Returns the value of this constant.
     * 
     * @return the value of this constant
     */
    public boolean getValue() {
        return constant;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return this; // experimental
        // return PropositionalConstant.create(constant);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return PropositionalConstant.create(constant);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public void getArrayVariables(Set<ArrayVariable> result,
            Set<SMTLibObject> done) {
        return;
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
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        return PropositionalConstant.create(constant);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getUninterpretedFunctions(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public void getFunctionMacroNames(Set<String> result, Set<SMTLibObject> done) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public void getFunctionMacros(Set<FunctionMacro> result,
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
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof PropositionalConstant))
            return false;
        return ((PropositionalConstant) obj).constant == constant;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return constant ? 1 : 0;
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
    public Term substituteTerm(Map<Token, ? extends Term> paramMap,
            Map<SMTLibObject, SMTLibObject> done) {
        return PropositionalConstant.create(constant);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, ? extends Term> paramMap,
            Map<SMTLibObject, SMTLibObject> done) {
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
    public PropositionalConstant flatten() {
        return PropositionalConstant.create(constant);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        return constant ? SExpressionConstants.TRUE
                : SExpressionConstants.FALSE;
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
    public Formula arrayReadsToUninterpretedFunctions(
            Set<Token> noDependenceVars) {
        // nothing to do
        return this;
    }

    @Override
    public Term arrayReadsToUninterpretedFunctionsTerm(
            Set<Token> noDependenceVars) {
        // nothing to do
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public PropositionalConstant substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions,
            Map<SMTLibObject, SMTLibObject> done) {
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
    /*
     * @Override public PropositionalTerm
     * uninterpretedPredicatesToAuxiliaryVariables( Formula topLeveFormula,
     * Set<Formula> constraints, Set<Token> noDependenceVars) { return
     * PropositionalConstant.create(constant); }
     */

    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = new TreeSet<Integer>();
        partitions.add(-1);
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

        Formula _this = this;
        if (notFlag == true) {
            // this.constant = !this.constant;
            _this = PropositionalConstant.create(!this.constant);
        }

        if (firstLevel == true) {
            List<Formula> literals = new ArrayList<Formula>();
            literals.add(_this);
            return OrFormula.generate(literals);
        }

        return _this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.Map)
     */
    @Override
    public PropositionalVariable tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding,
            Map<Formula, PropositionalVariable> done, int partition) {

        if (done.get(this) != null)
            return done.get(this);

        PropositionalVariable tseitinVar = Util.freshTseitinVar(partition);
        encoding.put(tseitinVar, this);
        done.put(this, tseitinVar);

        List<Formula> disjuncts = new ArrayList<Formula>(1);

        if (this.constant)
            disjuncts.add(tseitinVar);
        else
            disjuncts.add(NotFormula.create(tseitinVar));

        clauses.add(OrFormula.generate(disjuncts));

        return tseitinVar;
    }

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Formula uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {
        return this;
    }

    @Override
    public Term uninterpretedPredicatesToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {
        return this;
    }

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Formula uninterpretedFunctionsToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {
        return this;
    }

    @Override
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {
        return this;
    }

    @Override
    public Formula replaceEquivalences(Formula topLeveFormula,
            Map<EqualityFormula, String> replacements,
            Set<Token> noDependenceVars) {
        return this;
    }

    @Override
    public PropositionalTerm removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Collection)
     */
    @Override
    public PropositionalConstant removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints) {
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#writeOut(java.io.BufferedWriter,
     *      at.iaik.suraq.util.HashTagContainer, boolean)
     */
    @Override
    public void writeOut(BufferedWriter writer, HashTagContainer tagContainer,
            boolean handleThisWithTagContainer) throws IOException {
        writer.append(constant ? SExpressionConstants.TRUE.toString()
                : SExpressionConstants.FALSE.toString());

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#writeOut(java.io.BufferedWriter,
     *      at.iaik.suraq.util.HashTagContainer)
     */
    @Override
    public void writeOut(BufferedWriter writer, HashTagContainer tagContainer)
            throws IOException {
        writeOut(writer, tagContainer, true);

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#writeTo(java.io.Writer)
     */
    @Override
    public void writeTo(Writer writer) throws IOException {
        writer.write(constant ? SExpressionConstants.TRUE.toString()
                : SExpressionConstants.FALSE.toString());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#writeTo(java.io.Writer,
     *      java.util.Map)
     */
    @Override
    public void writeTo(Writer writer, Map<SMTLibObject, String> definitions)
            throws IOException {
        writer.write(constant ? SExpressionConstants.TRUE.toString()
                : SExpressionConstants.FALSE.toString());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getLiterals(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getLiterals(Set<Formula> result, Set<Formula> done) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#numAigNodes(java.util.Set)
     */
    @Override
    public int numAigNodes(Set<Formula> done) {
        return 0;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toAig(TreeMap, java.util.Map)
     */
    @Override
    public int toAig(TreeMap<Integer, Integer[]> aigNodes,
            Map<Formula, Integer> done) {
        return constant ? 1 : 0;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#size(boolean, java.util.Map)
     */
    @Override
    public BigInteger size(boolean expandDAG, Map<Formula, BigInteger> done) {
        if (done.get(this) != null) {
            if (expandDAG)
                return done.get(this);
            else
                return BigInteger.ZERO;
        }

        BigInteger result = BigInteger.ONE;
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#computeParents(java.util.Map,
     *      java.util.Set)
     */
    @Override
    public void computeParents(Map<Formula, Set<Formula>> parents,
            Set<Formula> done) {
        return; // Leaf node
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#computeSubformulasWithOnlyLeafChildren(java.util.Set,
     *      java.util.HashSet)
     */
    @Override
    public void computeSubformulasWithOnlyLeafChildren(
            Set<Formula> onlyLeafChildren, Set<Formula> leaves,
            Set<Formula> done) {
        if (done.contains(this))
            return;
        if (leaves.contains(this)) {
            done.add(this);
            return;
        }

        done.add(this);
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getTerms(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getTerms(Set<Term> result, Set<Formula> done) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#dependsOnlyOn(java.util.Set)
     */
    @Override
    public boolean dependsOnlyOn(Set<Formula> formulaSet) {
        return true;
    }

}
