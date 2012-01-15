/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * An if-then-else-style array term.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayIte extends ArrayTerm {

    /**
     * The condition.
     */
    private final Formula condition;

    /**
     * The then-branch.
     */
    private ArrayTerm thenBranch;

    /**
     * The else-branch
     */
    private ArrayTerm elseBranch;

    /**
     * 
     * Constructs a new <code>ArrayIte</code>.
     * 
     * @param condition
     *            the condition
     * @param thenBranch
     *            the value of the then-branch
     * @param elseBranch
     *            the value of the else-branch
     */
    public ArrayIte(Formula condition, ArrayTerm thenBranch,
            ArrayTerm elseBranch) {
        this.condition = condition;
        this.thenBranch = thenBranch;
        this.elseBranch = elseBranch;
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
    public ArrayTerm getThenBranch() {
        return thenBranch;
    }

    /**
     * Returns the else branch.
     * 
     * @return the <code>elseBranch</code>
     */
    public ArrayTerm getElseBranch() {
        return elseBranch;
    }

    /**
     * @see at.iaik.suraq.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return new ArrayIte(condition.deepFormulaCopy(),
                (ArrayTerm) thenBranch.deepTermCopy(),
                (ArrayTerm) elseBranch.deepTermCopy());
    }

    /**
     * @see at.iaik.suraq.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> result = thenBranch.getArrayVariables();
        result.addAll(elseBranch.getArrayVariables());
        result.addAll(condition.getArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> result = thenBranch.getDomainVariables();
        result.addAll(elseBranch.getDomainVariables());
        result.addAll(condition.getDomainVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getPropositionalVariables()
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
     * @see at.iaik.suraq.formula.Term#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = thenBranch.getFunctionMacroNames();
        result.addAll(elseBranch.getFunctionMacroNames());
        result.addAll(condition.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = thenBranch.getFunctionMacros();
        result.addAll(elseBranch.getFunctionMacros());
        result.addAll(condition.getFunctionMacros());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getUninterpretedFunctionNames()
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
        if (!(obj instanceof ArrayIte))
            return false;
        return ((ArrayIte) obj).thenBranch.equals(thenBranch)
                && ((ArrayIte) obj).elseBranch.equals(elseBranch)
                && ((ArrayIte) obj).condition.equals(condition);

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
     * @see at.iaik.suraq.formula.Term#getIndexSet()
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
     * @see at.iaik.suraq.formula.Term#substituteTerm(java.util.Map)
     */
    @Override
    public Term substituteTerm(Map<Token, Term> paramMap) {
        ArrayTerm convertedThenBranch = (ArrayTerm) thenBranch
                .substituteTerm(paramMap);
        ArrayTerm convertedElseBranch = (ArrayTerm) elseBranch
                .substituteTerm(paramMap);
        Formula convertedCondition = condition.substituteFormula(paramMap);
        return new ArrayIte(convertedCondition, convertedThenBranch,
                convertedElseBranch);
    }

    /**
     * Simplifies this term by first simplifying the condition, and subsequently
     * simplifying the ite, if the condition is a constant.
     * 
     * @return a <code>ArrayIte</code> term, which is simplified. Unchanged
     *         parts are not copied.
     */
    public ArrayTerm simplify() {

        Formula simplifiedCondition = condition.simplify();

        if (simplifiedCondition instanceof PropositionalConstant)
            if (((PropositionalConstant) simplifiedCondition).getValue())
                return thenBranch;
            else
                return elseBranch;

        if (thenBranch.equals(elseBranch))
            return thenBranch;

        return new ArrayIte(simplifiedCondition, thenBranch, elseBranch);
    }

    /**
     * @return a flattened copy of this term.
     */
    @Override
    public ArrayTerm flatten() {
        return new ArrayIte(condition.flatten(),
                (ArrayTerm) thenBranch.flatten(),
                (ArrayTerm) elseBranch.flatten());
    }

    /**
     * @see at.iaik.suraq.formula.Term#toSmtlibV2()
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
     * @see at.iaik.suraq.formula.Term#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        condition.arrayPropertiesToFiniteConjunctions(indexSet);
        thenBranch.arrayPropertiesToFiniteConjunctions(indexSet);
        elseBranch.arrayPropertiesToFiniteConjunctions(indexSet);
    }

    /**
     * @see at.iaik.suraq.formula.Term#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        condition.removeArrayEqualities();
        thenBranch.removeArrayEqualities();
        elseBranch.removeArrayEqualities();
    }

    /**
     * @see at.iaik.suraq.formula.Term#removeArrayWrites(at.iaik.suraq.formula.Formula)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        condition.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);

        if (thenBranch instanceof ArrayWrite)
            thenBranch = ((ArrayWrite) thenBranch).applyWriteAxiom(
                    topLevelFormula, constraints, noDependenceVars);
        else
            thenBranch.removeArrayWrites(topLevelFormula, constraints,
                    noDependenceVars);

        if (elseBranch instanceof ArrayWrite)
            elseBranch = ((ArrayWrite) elseBranch).applyWriteAxiom(
                    topLevelFormula, constraints, noDependenceVars);
        else
            elseBranch.removeArrayWrites(topLevelFormula, constraints,
                    noDependenceVars);

    }

    /**
     * @see at.iaik.suraq.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        condition.arrayReadsToUninterpretedFunctions(noDependenceVars);
        thenBranch.arrayReadsToUninterpretedFunctions(noDependenceVars);
        elseBranch.arrayReadsToUninterpretedFunctions(noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.formula.Term#getUninterpretedFunctions()
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
     * @see at.iaik.suraq.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.formula.UninterpretedFunction)
     */
    @Override
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        condition.substituteUninterpretedFunction(oldFunction, newFunction);
        thenBranch.substituteUninterpretedFunction(oldFunction, newFunction);
        elseBranch.substituteUninterpretedFunction(oldFunction, newFunction);
    }

    /**
     * @see at.iaik.suraq.formula.Term#makeArrayReadsSimple(java.util.Set,
     *      Formula, Set)
     */
    @Override
    public void makeArrayReadsSimple(Set<Formula> constraints,
            Formula topLevelFormula, Set<Token> noDependenceVars) {
        condition.makeArrayReadsSimple(constraints, topLevelFormula, noDependenceVars);
        thenBranch.makeArrayReadsSimple(constraints, topLevelFormula, noDependenceVars);
        elseBranch.makeArrayReadsSimple(constraints, topLevelFormula, noDependenceVars);
    }
}
