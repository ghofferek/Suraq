/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;

/**
 * Represents an if-then-else-style formula.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalIte extends BooleanCombinationFormula {

    /**
     * 
     */
    private static final long serialVersionUID = 8478152587648491278L;

    /**
     * The formula that represents the condition.
     */
    private final Formula condition;

    /**
     * The formula that represents the then-branch.
     */
    private final Formula thenBranch;

    /**
     * The formula that represents the else-branch.
     */
    private final Formula elseBranch;

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
    private PropositionalIte(Formula condition, Formula thenBranch,
            Formula elseBranch) {
        if (condition instanceof FormulaTerm)
            this.condition = ((FormulaTerm) condition).getFormula();
        else
            this.condition = condition;

        if (thenBranch instanceof FormulaTerm)
            this.thenBranch = ((FormulaTerm) thenBranch).getFormula();
        else
            this.thenBranch = thenBranch;

        if (elseBranch instanceof FormulaTerm)
            this.elseBranch = ((FormulaTerm) elseBranch).getFormula();
        else
            this.elseBranch = elseBranch;
    }
    
    public static PropositionalIte create(Formula condition,
            Formula thenBranch, Formula elseBranch) {
        return (PropositionalIte) FormulaCache.formula
                .put(new PropositionalIte(condition, thenBranch, elseBranch));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.BooleanCombinationFormula#getSubFormulas()
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
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return this; // experimental
        //return new PropositionalIte(condition.deepFormulaCopy(),
        //       thenBranch.deepFormulaCopy(), elseBranch.deepFormulaCopy());
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
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        return PropositionalIte.create(condition.negationNormalForm(),
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
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = thenBranch.getUninterpretedFunctionNames();
        result.addAll(elseBranch.getUninterpretedFunctionNames());
        result.addAll(condition.getUninterpretedFunctionNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = thenBranch.getFunctionMacroNames();
        result.addAll(elseBranch.getFunctionMacroNames());
        result.addAll(condition.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacros()
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
        if (this == obj)
            return true;
        if (!(obj instanceof PropositionalIte))
            return false;
        if (this.hashCode() != obj.hashCode())
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
        return condition.hashCode() * 31 * 31 + thenBranch.hashCode() * 31
                + elseBranch.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> result = thenBranch.getIndexSet();
        result.addAll(elseBranch.getIndexSet());
        result.addAll(condition.getIndexSet());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, ? extends Term> paramMap) {
        return PropositionalIte.create(condition.substituteFormula(paramMap),
                thenBranch.substituteFormula(paramMap),
                elseBranch.substituteFormula(paramMap));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualitiesTerm()
     */
    @Override
    public Formula removeArrayEqualities() {
        Formula condition = this.condition;
        Formula thenBranch = this.thenBranch;
        Formula elseBranch = this.elseBranch;

        if (condition instanceof ArrayEq)
            condition = ((ArrayEq) condition).toArrayProperties();
        else
            condition = condition.removeArrayEqualities();

        if (thenBranch instanceof ArrayEq)
            thenBranch = ((ArrayEq) thenBranch).toArrayProperties();
        else
            thenBranch = thenBranch.removeArrayEqualities();

        if (elseBranch instanceof ArrayEq)
            elseBranch = ((ArrayEq) elseBranch).toArrayProperties();
        else
            elseBranch = elseBranch.removeArrayEqualities();

        return PropositionalIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        Formula condition = this.condition;
        Formula thenBranch = this.thenBranch;
        Formula elseBranch = this.elseBranch;

        if (condition instanceof ArrayProperty)
            condition = ((ArrayProperty) condition)
                    .toFiniteConjunction(indexSet);
        else
            condition = condition.arrayPropertiesToFiniteConjunctions(indexSet);

        if (thenBranch instanceof ArrayProperty)
            thenBranch = ((ArrayProperty) thenBranch)
                    .toFiniteConjunction(indexSet);
        else
            thenBranch = thenBranch
                    .arrayPropertiesToFiniteConjunctions(indexSet);

        if (elseBranch instanceof ArrayProperty)
            elseBranch = ((ArrayProperty) elseBranch)
                    .toFiniteConjunction(indexSet);
        else
            elseBranch = elseBranch
                    .arrayPropertiesToFiniteConjunctions(indexSet);

        return PropositionalIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        Formula condition = this.condition.simplify();
        Formula thenBranch = this.thenBranch.simplify();
        Formula elseBranch = this.elseBranch.simplify();

        if (condition instanceof PropositionalConstant) {
            if (((PropositionalConstant) condition).getValue())
                return thenBranch;
            else
                return elseBranch;
        }

        if (thenBranch.equals(elseBranch))
            return thenBranch;

        return PropositionalIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        return PropositionalIte.create(condition.flatten(), thenBranch.flatten(),
                elseBranch.flatten());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {

        final boolean iteFree = false;

        if (iteFree) {
            List<Formula> disjuncts = new ArrayList<Formula>();
            List<Formula> conjunctsThen = new ArrayList<Formula>();
            List<Formula> conjunctsElse = new ArrayList<Formula>();
            conjunctsThen.add(condition);
            conjunctsThen.add(thenBranch);
            disjuncts.add(AndFormula.generate(conjunctsThen));
            conjunctsElse.add(NotFormula.create(condition));
            conjunctsElse.add(elseBranch);
            disjuncts.add(AndFormula.generate(conjunctsElse));
            Formula result = OrFormula.generate(disjuncts);
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
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        Formula condition = this.condition.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);
        Formula thenBranch = this.thenBranch.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);
        Formula elseBranch = this.elseBranch.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);
        return PropositionalIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Formula arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        Formula condition = this.condition.arrayReadsToUninterpretedFunctions(noDependenceVars);
        Formula thenBranch = this.thenBranch.arrayReadsToUninterpretedFunctions(noDependenceVars);
        Formula elseBranch = this.elseBranch.arrayReadsToUninterpretedFunctions(noDependenceVars);
        return PropositionalIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
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
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Formula substituteUninterpretedFunction(Map<Token, UninterpretedFunction> substitutions) {
        Formula condition = this.condition.substituteUninterpretedFunction(
                substitutions);
        Formula thenBranch = this.thenBranch.substituteUninterpretedFunction(
                substitutions);
        Formula elseBranch = this.elseBranch.substituteUninterpretedFunction(
                substitutions);
        return PropositionalIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        Formula condition = this.condition.makeArrayReadsSimple(
                topLevelFormula, constraints, noDependenceVars);
        Formula thenBranch = this.thenBranch.makeArrayReadsSimple(
                topLevelFormula, constraints, noDependenceVars);
        Formula elseBranch = this.elseBranch.makeArrayReadsSimple(
                topLevelFormula, constraints, noDependenceVars);
        return PropositionalIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*@Override
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
    }*/

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = condition.getPartitionsFromSymbols();
        partitions.addAll(thenBranch.getPartitionsFromSymbols());
        partitions.addAll(elseBranch.getPartitionsFromSymbols());

        return partitions;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm()
     */
    @Override
    public OrFormula transformToConsequentsForm() {
        throw new RuntimeException(
                "transformToConsequentsForm cannot be called on a Propositional Ite.\n"
                        + "Propositional Ite should not occur in the consequents of a proof.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm(boolean,
     *      boolean)
     */
    @Override
    public Formula transformToConsequentsForm(boolean notFlag,
            boolean firstLevel) {
        throw new RuntimeException(
                "transformToConsequentsForm cannot be called on a Propositional Ite.\n"
                        + "Propositional Ite should not occur in the consequents of a proof.");
    }

    /**
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     */
    @Override
    public int compareTo(SMTLibObject o) {
        return this.toString().compareTo(o.toString());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.List,
     *      java.util.Map)
     */
    @Override
    public PropositionalVariable tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding) {

        List<Formula> conjuncts = new ArrayList<Formula>(2);
        List<Formula> disjuncts = new ArrayList<Formula>(2);

        conjuncts.add(condition);
        conjuncts.add(thenBranch);
        disjuncts.add(AndFormula.generate(conjuncts));

        conjuncts.clear();
        conjuncts.add(NotFormula.create(condition));
        conjuncts.add(elseBranch);
        disjuncts.add(AndFormula.generate(conjuncts));

        return (OrFormula.generate(disjuncts)).tseitinEncode(clauses, encoding);

    }
    
    
    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Formula uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {
        Formula condition = this.condition;
        Formula thenBranch = this.thenBranch;
        Formula elseBranch = this.elseBranch;

        if (condition instanceof UninterpretedPredicateInstance)
            condition = ((UninterpretedPredicateInstance) condition)
                    .applyReplaceUninterpretedPredicates(topLeveFormula,
                            predicateInstances, instanceParameters,
                            noDependenceVars);
        else
            condition = condition.uninterpretedPredicatesToAuxiliaryVariables(
                    topLeveFormula, predicateInstances, instanceParameters,
                    noDependenceVars);

        if (thenBranch instanceof UninterpretedPredicateInstance)
            thenBranch = ((UninterpretedPredicateInstance) thenBranch)
                    .applyReplaceUninterpretedPredicates(topLeveFormula,
                            predicateInstances, instanceParameters,
                            noDependenceVars);
        else
            thenBranch = thenBranch
                    .uninterpretedPredicatesToAuxiliaryVariables(
                            topLeveFormula, predicateInstances,
                            instanceParameters, noDependenceVars);

        if (elseBranch instanceof UninterpretedPredicateInstance)
            elseBranch = ((UninterpretedPredicateInstance) elseBranch)
                    .applyReplaceUninterpretedPredicates(topLeveFormula,
                            predicateInstances, instanceParameters,
                            noDependenceVars);
        else
            elseBranch = elseBranch
                    .uninterpretedPredicatesToAuxiliaryVariables(
                            topLeveFormula, predicateInstances,
                            instanceParameters, noDependenceVars);
        
        return PropositionalIte.create(condition, thenBranch, elseBranch);
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
        Formula condition = this.condition
                .uninterpretedFunctionsToAuxiliaryVariables(topLeveFormula,
                        functionInstances, instanceParameters, noDependenceVars);
        Formula thenBranch = this.thenBranch
                .uninterpretedFunctionsToAuxiliaryVariables(topLeveFormula,
                        functionInstances, instanceParameters, noDependenceVars);
        Formula elseBranch = this.elseBranch
                .uninterpretedFunctionsToAuxiliaryVariables(topLeveFormula,
                        functionInstances, instanceParameters, noDependenceVars);
        return PropositionalIte.create(condition, thenBranch, elseBranch);
    } 
    
    

    @Override
    public Formula replaceEquivalences(Formula topLevelFormula, Map<EqualityFormula, String> replacements, Set<Token> noDependenceVars)
    {
        Formula condition = this.condition.replaceEquivalences(topLevelFormula, replacements, noDependenceVars);
        Formula thenBranch = this.thenBranch.replaceEquivalences(topLevelFormula, replacements, noDependenceVars);
        Formula elseBranch = this.elseBranch.replaceEquivalences(topLevelFormula, replacements, noDependenceVars);
        return PropositionalIte.create(condition, thenBranch, elseBranch);
    }
    

    @Override
    public Formula removeDomainITE(Formula topLevelFormula, Set<Token> noDependenceVars, List<Formula> andPreList)    {
        Formula condition = this.condition.removeDomainITE(topLevelFormula, noDependenceVars, andPreList);
        Formula thenBranch = this.thenBranch.removeDomainITE(topLevelFormula, noDependenceVars, andPreList);
        Formula elseBranch = this.elseBranch.removeDomainITE(topLevelFormula, noDependenceVars, andPreList);
        return PropositionalIte.create(condition, thenBranch, elseBranch);
    }
}
