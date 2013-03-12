/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.Util;

/**
 * A formula representing the negation of another one.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class NotFormula extends BooleanCombinationFormula {

    /**
     * 
     */
    private static final long serialVersionUID = -99679765405836941L;
    /**
     * The negated internal formula.
     */
    private final Formula formula;

    public static NotFormula create(Formula formula) {
        return FormulaCache.notFormula.put(new NotFormula(formula));
    }

    /**
     * 
     * Constructs a new <code>NotFormula</code>.
     * 
     * @param formula
     *            the negation of this formula.
     */
    private NotFormula(Formula formula) {
        if (formula instanceof FormulaTerm)
            this.formula = ((FormulaTerm) formula).getFormula();
        else
            this.formula = formula;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.BooleanCombinationFormula#getSubFormulas()
     */
    @Override
    public Collection<Formula> getSubFormulas() {
        List<Formula> list = new ArrayList<Formula>();
        list.add(formula);
        return list;
    }

    /**
     * Returns a copy of the negated formula.
     * 
     * @return A copy of the negated formula.
     */
    public Formula getNegatedFormula() {
        return formula.deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return this; // experimental
        // return NotFormula.create(formula.deepFormulaCopy());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        return formula.getArrayVariables();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        return formula.getDomainVariables();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        return formula.getPropositionalVariables();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {

        // And
        if (formula instanceof AndFormula) {
            List<Formula> subformulas = new ArrayList<Formula>();
            for (Formula subformula : ((AndOrXorFormula) formula).formulas)
                subformulas.add((NotFormula.create(subformula))
                        .negationNormalForm());
            return OrFormula.generate(subformulas);
        }

        // Or
        if (formula instanceof OrFormula) {
            List<Formula> subformulas = new ArrayList<Formula>();
            for (Formula subformula : ((AndOrXorFormula) formula).formulas)
                subformulas.add((NotFormula.create(subformula))
                        .negationNormalForm());
            return AndFormula.generate(subformulas);
        }

        // Xor
        if (formula instanceof XorFormula) {
            Formula converted = ((XorFormula) formula).toAndOrFormula();
            return (NotFormula.create(converted)).negationNormalForm();
        }

        // Not
        if (formula instanceof NotFormula) {
            return ((NotFormula) formula).formula.negationNormalForm();
        }

        // Equality
        if (formula instanceof EqualityFormula) {
            EqualityFormula eqFormula = (EqualityFormula) formula;
            if (eqFormula.isPair())
                return EqualityFormula.create(eqFormula.getTerms(),
                        !eqFormula.isEqual());

            AndFormula pairwise = eqFormula.toPairwise();
            return (NotFormula.create(pairwise)).negationNormalForm();
        }

        // ArrayProperty
        if (formula instanceof ArrayProperty) {
            throw new UnsupportedOperationException(
                    "NNF of array properties not implemented!");
        }

        // PropositionalConstant
        if (formula instanceof PropositionalConstant)
            return PropositionalConstant
                    .create(!((PropositionalConstant) formula).getValue());

        // PropositionalVariable
        if (formula instanceof PropositionalVariable)
            return this.deepFormulaCopy();

        // Implies
        if (formula instanceof ImpliesFormula) {
            ImpliesFormula impliesFormula = (ImpliesFormula) formula;
            List<Formula> list = new ArrayList<Formula>();
            list.add(impliesFormula.getLeftSide().negationNormalForm());
            list.add((NotFormula.create(impliesFormula.getRightSide()))
                    .negationNormalForm());
            return AndFormula.generate(list);
        }

        // MacroInstance
        if (formula instanceof PropositionalFunctionMacroInstance) {
            PropositionalFunctionMacro negatedMacro = ((PropositionalFunctionMacroInstance) formula)
                    .getMacro().negatedMacro();
            Map<Token, Term> paramMap = new HashMap<Token, Term>(
                    ((PropositionalFunctionMacroInstance) formula)
                            .getParamMap());
            return PropositionalFunctionMacroInstance.create(negatedMacro,
                    paramMap);
        }

        // PropositionalITE
        if (formula instanceof PropositionalIte) {
            PropositionalIte iteFormula = (PropositionalIte) formula;
            Formula thenBranch = (NotFormula.create(iteFormula.getThenBranch()))
                    .negationNormalForm();
            Formula elseBranch = (NotFormula.create(iteFormula.getElseBranch()))
                    .negationNormalForm();
            return PropositionalIte.create(iteFormula.getCondition()
                    .negationNormalForm(), thenBranch, elseBranch);
        }

        // something unexpected
        throw new SuraqException(
                "Unexpected formula type while trying to convert to NNF:"
                        + formula.getClass().toString());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        return formula.getUninterpretedFunctionNames();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        return formula.getFunctionMacroNames();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        return formula.getFunctionMacros();
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof NotFormula))
            return false;
        if (this.hashCode() != obj.hashCode())
            return false;
        return ((NotFormula) obj).formula.equals(formula);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return formula.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        return formula.getIndexSet();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, ? extends Term> paramMap) {
        return NotFormula.create(formula.substituteFormula(paramMap));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualitiesTerm()
     */
    @Override
    public Formula removeArrayEqualities() {
        Formula formula = this.formula;
        if (formula instanceof ArrayEq)
            formula = ((ArrayEq) formula).toArrayProperties();
        else
            formula = formula.removeArrayEqualities();
        return NotFormula.create(formula);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        Formula formula = this.formula;
        if (formula instanceof ArrayProperty)
            formula = ((ArrayProperty) formula).toFiniteConjunction(indexSet);
        else
            formula = formula.arrayPropertiesToFiniteConjunctions(indexSet);
        return NotFormula.create(formula);
    }

    /**
     * Checks whether this <code>NotFormula</code> is a negated propositional
     * variable. If so, the variable is returned (without the negation).
     * 
     * @return If this <code>NotFormula</code> is the negation of a
     *         <code>PropositionalVariable</code>, the variable is returned.
     *         Else, <code>null</code> is returned.
     */
    public PropositionalVariable isNegatedVariable() {
        if (!(formula instanceof PropositionalVariable))
            return null;
        else
            return (PropositionalVariable) formula;
    }

    /**
     * Checks whether this <code>NotFormula</code> is a negated propositional
     * constant. If so, the constant is returned (without the negation).
     * 
     * @return If this <code>NotFormula</code> is the negation of a
     *         <code>PropositionalConstant</code>, it is returned. Else,
     *         <code>null</code> is returned.
     */
    public PropositionalConstant isNegatedConstant() {
        if (!(formula instanceof PropositionalConstant))
            return null;
        else
            return (PropositionalConstant) formula;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        Formula formula = this.formula.simplify();

        if (formula instanceof PropositionalConstant)
            return PropositionalConstant
                    .create(!((PropositionalConstant) formula).getValue());

        if (formula instanceof NotFormula)
            return ((NotFormula) formula).formula;

        return NotFormula.create(formula);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        return NotFormula.create(formula.flatten());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        return new SExpression(SExpressionConstants.NOT, formula.toSmtlibV2());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        return NotFormula.create(formula.removeArrayWrites(topLevelFormula,
                constraints, noDependenceVars));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Formula arrayReadsToUninterpretedFunctions(
            Set<Token> noDependenceVars) {
        return NotFormula.create(formula
                .arrayReadsToUninterpretedFunctions(noDependenceVars));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        return formula.getUninterpretedFunctions();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Formula substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions) {
        return NotFormula.create(formula
                .substituteUninterpretedFunction(substitutions));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        return NotFormula.create(formula.makeArrayReadsSimple(topLevelFormula,
                constraints, noDependenceVars));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*
     * @Override public Formula uninterpretedPredicatesToAuxiliaryVariables(
     * Formula topLeveFormula, Set<Formula> constraints, Set<Token>
     * noDependenceVars) { return NotFormula.create(
     * formula.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars)); }
     */

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {

        return formula.getPartitionsFromSymbols();
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

        Formula notFormula;

        if (isValidChild(this.formula)) {

            notFormula = this.formula.transformToConsequentsForm(!notFlag,
                    false);

            if (firstLevel == true) {
                if (Util.isLiteral(notFormula)) {
                    List<Formula> literals = new ArrayList<Formula>();
                    literals.add(notFormula);
                    Formula orFormula = OrFormula.generate(literals);
                    return orFormula;
                } else if (notFormula instanceof OrFormula) {
                    return notFormula;
                } else
                    throw new RuntimeException(
                            "Clausel should always be a Or Formula");
            }

            return notFormula;

        } else
            throw new RuntimeException("Not formula has no valid child.");
    }

    /**
     * Checks if a given formula is a valid child for a NOT Formula.
     * 
     * @param formula
     *            formula to check
     * @return true, iff formula is valid
     */
    public boolean isValidChild(Formula formula) {
        if (formula instanceof OrFormula)
            return true;
        if (formula instanceof AndFormula)
            return true;
        if (formula instanceof NotFormula)
            return true;
        if (formula instanceof ImpliesFormula)
            return true;
        if (Util.isLiteral(formula))
            return true;
        return false;
    }

    /**
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     */
    @Override
    public int compareTo(SMTLibObject o) {
        return this.toString().compareTo(o.toString());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.Map)
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

        Formula tseitinVarForSubformula = formula.tseitinEncode(clauses,
                encoding);
        assert (Util.isLiteral(tseitinVarForSubformula));

        List<Formula> disjuncts = new ArrayList<Formula>(2);
        disjuncts.add(tseitinVar);
        disjuncts.add(tseitinVarForSubformula);
        clauses.add(OrFormula.generate(disjuncts));

        disjuncts.clear();
        disjuncts.add(NotFormula.create(tseitinVar));
        disjuncts.add(NotFormula.create(tseitinVarForSubformula));
        clauses.add(OrFormula.generate(disjuncts));

        return tseitinVar;
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
        Formula formula = this.formula;
        if (formula instanceof UninterpretedPredicateInstance)
            formula = ((UninterpretedPredicateInstance) formula)
                    .applyReplaceUninterpretedPredicates(topLeveFormula,
                            predicateInstances, instanceParameters,
                            noDependenceVars);
        else
            formula = formula.uninterpretedPredicatesToAuxiliaryVariables(
                    topLeveFormula, predicateInstances, instanceParameters,
                    noDependenceVars);
        return NotFormula.create(formula);
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
        return NotFormula
                .create(formula.uninterpretedFunctionsToAuxiliaryVariables(
                        topLeveFormula, functionInstances, instanceParameters,
                        noDependenceVars));
    }

    @Override
    public Formula replaceEquivalences(Formula topLeveFormula,
            Map<EqualityFormula, String> replacements,
            Set<Token> noDependenceVars) {
        return NotFormula.create(formula.replaceEquivalences(topLeveFormula,
                replacements, noDependenceVars));
    }

    @Override
    public Formula removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        return NotFormula.create(formula.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList));
    }
}
