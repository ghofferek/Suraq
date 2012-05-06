/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class FormulaTerm extends PropositionalTerm {

    /**
     * The formula that represents this term.
     */
    private Formula formula;

    /**
     * 
     * Constructs a new <code>FormulaTerm</code>.
     * 
     * @param formula
     *            the formula that represents this term.
     */
    public FormulaTerm(Formula formula) {
        this.formula = formula.deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return new FormulaTerm(formula);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        return new FormulaTerm(formula.negationNormalForm());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(java.util.Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, Term> paramMap) {
        return new FormulaTerm(formula.substituteFormula(paramMap));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.PropositionalTerm#flatten()
     */
    @Override
    public PropositionalTerm flatten() {
        return new FormulaTerm(formula.flatten());
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
     * @see at.iaik.suraq.smtlib.formula.Term#substituteTerm(java.util.Map)
     */
    @Override
    public Term substituteTerm(Map<Token, Term> paramMap) {
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
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        if (formula instanceof ArrayProperty)
            ((ArrayProperty) formula).toFiniteConjunction(indexSet);
        else
            formula.arrayPropertiesToFiniteConjunctions(indexSet);

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        formula.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions(java.util.Set)
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        formula.arrayReadsToUninterpretedFunctions(noDependenceVars);

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
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        if (formula instanceof UninterpretedPredicateInstance) {
            if (((UninterpretedFunctionInstance) formula).getFunction().equals(
                    oldFunction)) {
                try {
                    formula = new UninterpretedPredicateInstance(newFunction,
                            ((UninterpretedFunctionInstance) formula)
                                    .getParameters());
                } catch (SuraqException exc) {
                    throw new RuntimeException(
                            "Unexpected situation while subsituting uninterpreted function");
                }
            }
            for (Term param : ((UninterpretedFunctionInstance) formula)
                    .getParameters())
                param.substituteUninterpretedFunction(oldFunction, newFunction);
        }
        formula.substituteUninterpretedFunction(oldFunction, newFunction);

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public void makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        formula.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public FormulaTerm uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        return new FormulaTerm(
                formula.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars));
    }

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getAssertPartition() {
        return formula.getAssertPartition();
    }

}
