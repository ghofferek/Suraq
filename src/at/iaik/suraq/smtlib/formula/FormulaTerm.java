/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.HashTagContainer;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class FormulaTerm extends PropositionalTerm {

    /**
     * 
     */
    private static final long serialVersionUID = -7262583554346618516L;
    /**
     * The formula that represents this term.
     */
    private final Formula formula;

    /**
     * 
     * Constructs a new <code>FormulaTerm</code>.
     * 
     * @param formula
     *            the formula that represents this term.
     */
    private FormulaTerm(Formula formula) {
        this.formula = formula.deepFormulaCopy();
    }

    /**
     * Creates and returns a new <code>FormulaTerm</code> for the given
     * <code>formula</code>, unless the <code>formula</code> is already a
     * <code>PropositionalTerm</code>, in which case it is returned unaltered.
     * 
     * @param formula
     *            the formula to encapsulate
     * @return either a <code>FormulaTerm</code> encapsulating
     *         <code>formula</code>, or <code>formula</code> itself, if it
     *         already is a <code>PropositionalTerm</code>.
     */
    public static PropositionalTerm create(Formula formula) {
        if (formula instanceof PropositionalTerm)
            return (PropositionalTerm) formula;
        else
            return FormulaCache.formulaTerm.put(new FormulaTerm(formula));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return this; // experimental
        // return new FormulaTerm(formula);
    }

    /**
     * returns the formula of the <code>FormulaTerm</code>.
     * 
     * @return the formula
     */
    public Formula getFormula() {
        return formula.deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        return FormulaTerm.create(formula.negationNormalForm());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, ? extends Term> paramMap) {
        return FormulaTerm.create(formula.substituteFormula(paramMap));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.PropositionalTerm#flatten()
     */
    @Override
    public PropositionalTerm flatten() {
        return FormulaTerm.create(formula.flatten());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return (FormulaTerm) deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        return formula.getArrayVariables();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        return formula.getDomainVariables();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        return formula.getPropositionalVariables();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        return formula.getFunctionMacroNames();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        return formula.getFunctionMacros();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        return formula.getUninterpretedFunctionNames();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteTerm(Map)
     */
    @Override
    public Term substituteTerm(Map<Token, ? extends Term> paramMap) {
        return (FormulaTerm) substituteFormula(paramMap);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        return formula.getIndexSet();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        return formula.toSmtlibV2();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        if (formula instanceof ArrayProperty)
            return FormulaTerm.create(((ArrayProperty) formula)
                    .toFiniteConjunction(indexSet));
        // TODO: the line before maybe returns something wrong because
        // toFiniteConjunction returns And
        else
            return FormulaTerm.create(formula
                    .arrayPropertiesToFiniteConjunctions(indexSet));
    }

    @Override
    public Term arrayPropertiesToFiniteConjunctionsTerm(Set<DomainTerm> indexSet) {
        if (formula instanceof ArrayProperty)
            return FormulaTerm.create(((ArrayProperty) formula)
                    .toFiniteConjunction(indexSet));
        // TODO: the line before maybe returns something wrong because
        // toFiniteConjunction returns And
        else
            return FormulaTerm.create(formula
                    .arrayPropertiesToFiniteConjunctions(indexSet));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        return FormulaTerm.create(formula.removeArrayWrites(topLevelFormula,
                constraints, noDependenceVars));
    }

    @Override
    public Term removeArrayWritesTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        return FormulaTerm.create(formula.removeArrayWrites(topLevelFormula,
                constraints, noDependenceVars));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions(java.util.Set)
     */
    @Override
    public Formula arrayReadsToUninterpretedFunctions(
            Set<Token> noDependenceVars) {
        return FormulaTerm.create(formula
                .arrayReadsToUninterpretedFunctions(noDependenceVars));
    }

    @Override
    public Term arrayReadsToUninterpretedFunctionsTerm(
            Set<Token> noDependenceVars) {
        return FormulaTerm.create(formula
                .arrayReadsToUninterpretedFunctions(noDependenceVars));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        return formula.getUninterpretedFunctions();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(at.iaik.suraq.sexp.Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Formula substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions) {
        Formula formula = this.formula;

        if (formula instanceof UninterpretedPredicateInstance) {
            Token key = ((UninterpretedFunctionInstance) formula).getFunction()
                    .getName();
            if (substitutions.containsKey(key)) {
                try {
                    formula = UninterpretedPredicateInstance.create(
                            substitutions.get(key),
                            ((UninterpretedFunctionInstance) formula)
                                    .getParameters());
                } catch (SuraqException exc) {
                    throw new RuntimeException(
                            "Unexpected situation while subsituting uninterpreted function");
                }
            }
            // if (((UninterpretedFunctionInstance)
            // formula).getFunction().equals(
            // oldFunction)) {
            // try {
            // formula = UninterpretedPredicateInstance.create(newFunction,
            // ((UninterpretedFunctionInstance) formula)
            // .getParameters());
            // } catch (SuraqException exc) {
            // throw new RuntimeException(
            // "Unexpected situation while subsituting uninterpreted function");
            // }
            // }
            List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
            for (Term param : ((UninterpretedFunctionInstance) formula)
                    .getParameters())
                paramNew.add((DomainTerm) param
                        .substituteUninterpretedFunctionTerm(substitutions));
            try {
                formula = UninterpretedPredicateInstance.create(
                        ((UninterpretedPredicateInstance) formula)
                                .getFunction(), paramNew, assertPartition);
            } catch (Exception e) {
                e.printStackTrace();
                throw new RuntimeException(e);
            }
            // (UninterpretedFunction function,List<DomainTerm> parameters, int
            // partition
            // ... create new formula with parameters...

        }
        formula = formula.substituteUninterpretedFunction(substitutions);
        return FormulaTerm.create(formula);
    }

    @Override
    public Term substituteUninterpretedFunctionTerm(
            Map<Token, UninterpretedFunction> substitutions) {
        Formula formula = this.formula;

        if (formula instanceof UninterpretedPredicateInstance) {
            Token key = ((UninterpretedFunctionInstance) formula).getFunction()
                    .getName();
            if (substitutions.containsKey(key)) {
                try {
                    formula = UninterpretedPredicateInstance.create(
                            substitutions.get(key),
                            ((UninterpretedFunctionInstance) formula)
                                    .getParameters());
                } catch (SuraqException exc) {
                    throw new RuntimeException(
                            "Unexpected situation while subsituting uninterpreted function");
                }
            }

            // if (((UninterpretedFunctionInstance)
            // formula).getFunction().equals(
            // oldFunction)) {
            // try {
            // formula = UninterpretedPredicateInstance.create(newFunction,
            // ((UninterpretedFunctionInstance) formula)
            // .getParameters());
            // } catch (SuraqException exc) {
            // throw new RuntimeException(
            // "Unexpected situation while subsituting uninterpreted function");
            // }
            // }

            List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
            for (Term param : ((UninterpretedFunctionInstance) formula)
                    .getParameters())
                paramNew.add((DomainTerm) param
                        .substituteUninterpretedFunctionTerm(substitutions));
            try {
                formula = UninterpretedPredicateInstance.create(
                        ((UninterpretedPredicateInstance) formula)
                                .getFunction(), paramNew, assertPartition);
            } catch (Exception e) {
                e.printStackTrace();
                throw new RuntimeException(e);
            }
            // (UninterpretedFunction function,List<DomainTerm> parameters, int
            // partition
            // ... create new formula with parameters...

        }
        formula = formula.substituteUninterpretedFunction(substitutions);
        return FormulaTerm.create(formula);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        return FormulaTerm.create(formula.makeArrayReadsSimple(topLevelFormula,
                constraints, noDependenceVars));
    }

    @Override
    public Term makeArrayReadsSimpleTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        return FormulaTerm.create(formula.makeArrayReadsSimple(topLevelFormula,
                constraints, noDependenceVars));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*
     * @Override public FormulaTerm uninterpretedPredicatesToAuxiliaryVariables(
     * Formula topLeveFormula, Set<Formula> constraints, Set<Token>
     * noDependenceVars) { return new FormulaTerm(
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
        return this.formula.transformToConsequentsForm(notFlag, firstLevel);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return formula.hashCode();
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof FormulaTerm))
            return false;
        if (this.formula == ((FormulaTerm) obj).formula)
            return true;
        if (this.hashCode() != obj.hashCode())
            return false;

        return formula.equals(((FormulaTerm) obj).formula);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.List,
     *      java.util.Map)
     */
    @Override
    public Formula tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding, int partition) {

        return formula.tseitinEncode(clauses, encoding, partition);
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
        return FormulaTerm.create(formula);
    }

    @Override
    public Term uninterpretedPredicatesToAuxiliaryVariablesTerm(
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
        return FormulaTerm.create(formula);
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
        return FormulaTerm
                .create(formula.uninterpretedFunctionsToAuxiliaryVariables(
                        topLeveFormula, functionInstances, instanceParameters,
                        noDependenceVars));
    }

    @Override
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {
        return FormulaTerm
                .create(formula.uninterpretedFunctionsToAuxiliaryVariables(
                        topLeveFormula, functionInstances, instanceParameters,
                        noDependenceVars));
    }

    @Override
    public Formula replaceEquivalences(Formula topLevelFormula,
            Map<EqualityFormula, String> replacements,
            Set<Token> noDependenceVars) {
        Formula formula = this.formula.replaceEquivalences(topLevelFormula,
                replacements, noDependenceVars);
        return FormulaTerm.create(formula);
    }

    @Override
    public PropositionalTerm removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        Formula formula = this.formula.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList);
        return FormulaTerm.create(formula);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedFunctionsBackToArrayReads(java.util.Set)
     */
    @Override
    public PropositionalTerm uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars) {
        return FormulaTerm.create(formula
                .uninterpretedFunctionsBackToArrayReads(arrayVars));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Collection)
     */
    @Override
    public PropositionalTerm removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints) {
        return FormulaTerm.create(formula.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#writeOut(java.io.BufferedWriter,
     *      at.iaik.suraq.util.HashTagContainer, boolean)
     */
    @Override
    public void writeOut(BufferedWriter writer, HashTagContainer tagContainer,
            boolean handleThisWithTagContainer) throws IOException {
        formula.writeOut(writer, tagContainer, handleThisWithTagContainer);

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

}
