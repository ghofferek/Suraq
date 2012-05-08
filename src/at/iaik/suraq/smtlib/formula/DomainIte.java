/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * An if-then-else-style domain term.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class DomainIte extends DomainTerm {

    /**
     * The condition.
     */
    private final Formula condition;

    /**
     * The then-branch.
     */
    private DomainTerm thenBranch;

    /**
     * The else-branch
     */
    private DomainTerm elseBranch;

    /**
     * 
     * Constructs a new <code>DomainIte</code>.
     * 
     * @param condition
     *            the condition
     * @param thenBranch
     *            the value of the then-branch
     * @param elseBranch
     *            the value of the else-branch
     */
    public DomainIte(Formula condition, DomainTerm thenBranch,
            DomainTerm elseBranch) {
        this.condition = condition;
        this.thenBranch = thenBranch;
        this.elseBranch = elseBranch;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#isEvar(java.util.Collection)
     */
    @Override
    public boolean isEvar(Collection<DomainVariable> uVars) {
        // not applicable to DomainIte
        return false;
    }

    /**
     * Returns the condition.
     * 
     * @return the <code>condition</code>
     */
    public Formula getCondition() {
        return condition;
    }

    /**
     * Returns the then branch.
     * 
     * @return the <code>thenBranch</code>
     */
    public DomainTerm getThenBranch() {
        return thenBranch;
    }

    /**
     * Returns the else branch.
     * 
     * @return the <code>elseBranch</code>
     */
    public DomainTerm getElseBranch() {
        return elseBranch;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public DomainTerm deepTermCopy() {
        return new DomainIte(condition.deepFormulaCopy(),
                thenBranch.deepTermCopy(), elseBranch.deepTermCopy());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> result = thenBranch.getArrayVariables();
        result.addAll(elseBranch.getArrayVariables());
        result.addAll(condition.getArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> result = thenBranch.getDomainVariables();
        result.addAll(elseBranch.getDomainVariables());
        result.addAll(condition.getDomainVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> result = thenBranch
                .getPropositionalVariables();
        result.addAll(elseBranch.getPropositionalVariables());
        result.addAll(condition.getPropositionalVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = thenBranch.getFunctionMacroNames();
        result.addAll(elseBranch.getFunctionMacroNames());
        result.addAll(condition.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = thenBranch.getFunctionMacros();
        result.addAll(elseBranch.getFunctionMacros());
        result.addAll(condition.getFunctionMacros());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = thenBranch.getUninterpretedFunctionNames();
        result.addAll(elseBranch.getUninterpretedFunctionNames());
        result.addAll(condition.getUninterpretedFunctionNames());
        return result;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof DomainIte))
            return false;
        return ((DomainIte) obj).thenBranch.equals(thenBranch)
                && ((DomainIte) obj).elseBranch.equals(elseBranch)
                && ((DomainIte) obj).condition.equals(condition);

    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return condition.hashCode() ^ thenBranch.hashCode()
                ^ elseBranch.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> result = new HashSet<DomainTerm>();
        result.addAll(thenBranch.getIndexSet());
        result.addAll(elseBranch.getIndexSet());
        result.addAll(condition.getIndexSet());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteTerm(java.util.Map)
     */
    @Override
    public Term substituteTerm(Map<Token, Term> paramMap) {
        DomainTerm convertedThenBranch = (DomainTerm) thenBranch
                .substituteTerm(paramMap);
        DomainTerm convertedElseBranch = (DomainTerm) elseBranch
                .substituteTerm(paramMap);
        Formula convertedCondition = condition.substituteFormula(paramMap);
        return new DomainIte(convertedCondition, convertedThenBranch,
                convertedElseBranch);
    }

    /**
     * Simplifies this term by first simplifying the condition, and subsequently
     * simplifying the ite, if the condition is a constant.
     * 
     * @return a <code>DomainIte</code> term, which is simplified. Unchanged
     *         parts are not copied.
     */
    public DomainTerm simplify() {

        Formula simplifiedCondition = condition.simplify();

        if (simplifiedCondition instanceof PropositionalConstant)
            if (((PropositionalConstant) simplifiedCondition).getValue())
                return thenBranch;
            else
                return elseBranch;

        if (thenBranch.equals(elseBranch))
            return thenBranch;

        return new DomainIte(simplifiedCondition, thenBranch, elseBranch);
    }

    /**
     * @return a flattened copy of this term.
     */
    @Override
    public DomainTerm flatten() {
        return new DomainIte(condition.flatten(),
                (DomainTerm) thenBranch.flatten(),
                (DomainTerm) elseBranch.flatten());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        SExpression[] expr = new SExpression[4];
        expr[0] = SExpressionConstants.ITE;
        expr[1] = condition.toSmtlibV2();
        expr[2] = thenBranch.toSmtlibV2();
        expr[3] = elseBranch.toSmtlibV2();
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        condition.arrayPropertiesToFiniteConjunctions(indexSet);
        thenBranch.arrayPropertiesToFiniteConjunctions(indexSet);
        elseBranch.arrayPropertiesToFiniteConjunctions(indexSet);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        condition.removeArrayEqualities();
        thenBranch.removeArrayEqualities();
        elseBranch.removeArrayEqualities();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        condition.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);
        thenBranch.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);
        elseBranch.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        condition.arrayReadsToUninterpretedFunctions(noDependenceVars);

        if (thenBranch instanceof ArrayRead)
            thenBranch = ((ArrayRead) thenBranch)
                    .toUninterpretedFunctionInstance(noDependenceVars);
        else
            thenBranch.arrayReadsToUninterpretedFunctions(noDependenceVars);

        if (elseBranch instanceof ArrayRead)
            elseBranch = ((ArrayRead) elseBranch)
                    .toUninterpretedFunctionInstance(noDependenceVars);
        else
            elseBranch.arrayReadsToUninterpretedFunctions(noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        Set<UninterpretedFunction> result = thenBranch
                .getUninterpretedFunctions();
        result.addAll(elseBranch.getUninterpretedFunctions());
        result.addAll(condition.getUninterpretedFunctions());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        condition.substituteUninterpretedFunction(oldFunction, newFunction);
        thenBranch.substituteUninterpretedFunction(oldFunction, newFunction);
        elseBranch.substituteUninterpretedFunction(oldFunction, newFunction);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public void makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        condition.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
        thenBranch.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
        elseBranch.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public DomainTerm uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        return new DomainIte(
                condition.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars),
                thenBranch.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars),
                elseBranch.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars));
    }

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getAssertPartition() {
        Set<Integer> partitions = condition.getAssertPartition();
        partitions.addAll(thenBranch.getAssertPartition());
        partitions.addAll(elseBranch.getAssertPartition());

        return partitions;
    }
}