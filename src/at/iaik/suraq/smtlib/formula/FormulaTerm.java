/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.List;
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
     * 
     */
    private static final long serialVersionUID = -7262583554346618516L;
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
            return new FormulaTerm(formula);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return new FormulaTerm(formula);
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
        return new FormulaTerm(formula.negationNormalForm());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, ? extends Term> paramMap) {
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
    /*@Override
    public FormulaTerm uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        return new FormulaTerm(
                formula.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars));
    }*/

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
    public PropositionalVariable tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding) {

        return formula.tseitinEncode(clauses, encoding);
    }

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public void uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
    	
		    	if (formula instanceof UninterpretedPredicateInstance)
		    		formula = ((UninterpretedPredicateInstance) formula).applyReplaceUninterpretedPredicates(topLeveFormula,
							      predicateInstances, instanceParameters, noDependenceVars);
				else
					formula.uninterpretedPredicatesToAuxiliaryVariables(
								  topLeveFormula, predicateInstances, instanceParameters, noDependenceVars);
    }

    
    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public void uninterpretedFunctionsToAuxiliaryVariables(
            Formula topLeveFormula, Map<String,List<DomainVariable>> functionInstances, 
            Map<DomainVariable, List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
		       formula.uninterpretedFunctionsToAuxiliaryVariables(
		                        topLeveFormula, functionInstances, instanceParameters, noDependenceVars);
    }  
    

    @Override
    public Formula replaceEquivalences(Formula topLevelFormula, Map<EqualityFormula, String> replacements, Set<Token> noDependenceVars)
    {
        formula = formula.replaceEquivalences(topLevelFormula, replacements, noDependenceVars);
        return this;
    }
    
    

    @Override
    public Formula removeDomainITE(Formula topLevelFormula, Set<Token> noDependenceVars, List<Formula> andPreList)
    {
        formula = formula.removeDomainITE(topLevelFormula, noDependenceVars, andPreList);
        return this;
    }
    
}
