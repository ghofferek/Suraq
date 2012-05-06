/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * Represents an if-then-else-style formula.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalIte extends BooleanCombinationFormula {

    /**
     * The formula that represents the condition.
     */
    private Formula condition;

    /**
     * The formula that represents the then-branch.
     */
    private Formula thenBranch;

    /**
     * The formula that represents the else-branch.
     */
    private Formula elseBranch;

    /**
     * 
     * Constructs a new <code>PropositionalIte</code>.
     * 
     * @param condition
     *            the formula that represents the condition
     * @param thenBranch
     *            the formula that represents the then-branch
     * @param elseBranch
     *            the formula that represents the else-branch
     */
    public PropositionalIte(Formula condition, Formula thenBranch,
            Formula elseBranch) {
        this.condition = condition;
        this.thenBranch = thenBranch;
        this.elseBranch = elseBranch;
    }

    /**
     * @see at.iaik.suraq.formula.BooleanCombinationFormula#getSubFormulas()
     */
    @Override
    public Collection<Formula> getSubFormulas() {
        List<Formula> list = new ArrayList<Formula>();
        list.add(condition);
        list.add(thenBranch);
        list.add(elseBranch);
        return list;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return new PropositionalIte(condition.deepFormulaCopy(),
                thenBranch.deepFormulaCopy(), elseBranch.deepFormulaCopy());
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
     * @see at.iaik.suraq.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        return new PropositionalIte(condition.negationNormalForm(),
                thenBranch.negationNormalForm(),
                elseBranch.negationNormalForm());
    }

    /**
     * @return the <code>condition</code>
     */
    public Formula getCondition() {
        return condition;
    }

    /**
     * @return the <code>thenBranch</code>
     */
    public Formula getThenBranch() {
        return thenBranch;
    }

    /**
     * @return the <code>elseBranch</code>
     */
    public Formula getElseBranch() {
        return elseBranch;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = thenBranch.getUninterpretedFunctionNames();
        result.addAll(elseBranch.getUninterpretedFunctionNames());
        result.addAll(condition.getUninterpretedFunctionNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = thenBranch.getFunctionMacroNames();
        result.addAll(elseBranch.getFunctionMacroNames());
        result.addAll(condition.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = thenBranch.getFunctionMacros();
        result.addAll(elseBranch.getFunctionMacros());
        result.addAll(condition.getFunctionMacros());
        return result;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof PropositionalIte))
            return false;
        return ((PropositionalIte) obj).thenBranch.equals(thenBranch)
                && ((PropositionalIte) obj).elseBranch.equals(elseBranch)
                && ((PropositionalIte) obj).condition.equals(condition);

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
     * @see at.iaik.suraq.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> result = thenBranch.getIndexSet();
        result.addAll(elseBranch.getIndexSet());
        result.addAll(condition.getIndexSet());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#substituteFormula(java.util.Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, Term> paramMap) {
        return new PropositionalIte(condition.substituteFormula(paramMap),
                thenBranch.substituteFormula(paramMap),
                elseBranch.substituteFormula(paramMap));
    }

    /**
     * @see at.iaik.suraq.formula.Formula#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        if (condition instanceof ArrayEq)
            condition = ((ArrayEq) condition).toArrayProperties();
        else
            condition.removeArrayEqualities();

        if (thenBranch instanceof ArrayEq)
            thenBranch = ((ArrayEq) thenBranch).toArrayProperties();
        else
            thenBranch.removeArrayEqualities();

        if (elseBranch instanceof ArrayEq)
            elseBranch = ((ArrayEq) elseBranch).toArrayProperties();
        else
            elseBranch.removeArrayEqualities();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        if (condition instanceof ArrayProperty)
            condition = ((ArrayProperty) condition)
                    .toFiniteConjunction(indexSet);
        else
            condition.arrayPropertiesToFiniteConjunctions(indexSet);

        if (thenBranch instanceof ArrayProperty)
            thenBranch = ((ArrayProperty) thenBranch)
                    .toFiniteConjunction(indexSet);
        else
            thenBranch.arrayPropertiesToFiniteConjunctions(indexSet);

        if (elseBranch instanceof ArrayProperty)
            elseBranch = ((ArrayProperty) elseBranch)
                    .toFiniteConjunction(indexSet);
        else
            elseBranch.arrayPropertiesToFiniteConjunctions(indexSet);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        condition = condition.simplify();
        thenBranch = thenBranch.simplify();
        elseBranch = elseBranch.simplify();

        if (condition instanceof PropositionalConstant) {
            if (((PropositionalConstant) condition).getValue())
                return thenBranch;
            else
                return elseBranch;
        }

        if (thenBranch.equals(elseBranch))
            return thenBranch;

        return this;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        return new PropositionalIte(condition.flatten(), thenBranch.flatten(),
                elseBranch.flatten());
    }

    /**
     * @see at.iaik.suraq.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {

        final boolean iteFree = true;

        if (iteFree) {
            List<Formula> disjuncts = new ArrayList<Formula>();
            List<Formula> conjunctsThen = new ArrayList<Formula>();
            List<Formula> conjunctsElse = new ArrayList<Formula>();
            conjunctsThen.add(condition);
            conjunctsThen.add(thenBranch);
            disjuncts.add(new AndFormula(conjunctsThen));
            conjunctsElse.add(new NotFormula(condition));
            conjunctsElse.add(elseBranch);
            disjuncts.add(new AndFormula(conjunctsElse));
            Formula result = new OrFormula(disjuncts);
            return result.toSmtlibV2();
        } else {
            SExpression[] expr = new SExpression[4];
            expr[0] = SExpressionConstants.ITE;
            expr[1] = condition.toSmtlibV2();
            expr[2] = thenBranch.toSmtlibV2();
            expr[3] = elseBranch.toSmtlibV2();
            return new SExpression(expr);
        }
    }

    /**
     * @see at.iaik.suraq.formula.Formula#removeArrayWrites(at.iaik.suraq.formula.Formula)
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
     * @see at.iaik.suraq.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        condition.arrayReadsToUninterpretedFunctions(noDependenceVars);
        thenBranch.arrayReadsToUninterpretedFunctions(noDependenceVars);
        elseBranch.arrayReadsToUninterpretedFunctions(noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getUninterpretedFunctions()
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
     * @see at.iaik.suraq.formula.Formula#substituteUninterpretedFunction(Token,
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
     * @see at.iaik.suraq.formula.Formula#makeArrayReadsSimple(at.iaik.suraq.formula.Formula,
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
     * @see at.iaik.suraq.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        return new PropositionalIte(
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
