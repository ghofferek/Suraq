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

/**
 * A formula representing the negation of another one.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class NotFormula extends BooleanCombinationFormula {

    /**
     * The negated internal formula.
     */
    private Formula formula;

    /**
     * 
     * Constructs a new <code>NotFormula</code>.
     * 
     * @param formula
     *            the negation of this formula.
     */
    public NotFormula(Formula formula) {
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
        return new NotFormula(formula.deepFormulaCopy());
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
                subformulas.add((new NotFormula(subformula))
                        .negationNormalForm());
            return new OrFormula(subformulas);
        }

        // Or
        if (formula instanceof OrFormula) {
            List<Formula> subformulas = new ArrayList<Formula>();
            for (Formula subformula : ((AndOrXorFormula) formula).formulas)
                subformulas.add((new NotFormula(subformula))
                        .negationNormalForm());
            return new AndFormula(subformulas);
        }

        // Xor
        if (formula instanceof XorFormula) {
            Formula converted = ((XorFormula) formula).toAndOrFormula();
            return (new NotFormula(converted)).negationNormalForm();
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
            return (new NotFormula(pairwise)).negationNormalForm();
        }

        // ArrayProperty
        if (formula instanceof ArrayProperty) {
            throw new UnsupportedOperationException(
                    "NNF of array properties not implemented!");
        }

        // PropositionalConstant
        if (formula instanceof PropositionalConstant)
            return new PropositionalConstant(
                    !((PropositionalConstant) formula).getValue());

        // PropositionalVariable
        if (formula instanceof PropositionalVariable)
            return this.deepFormulaCopy();

        // Implies
        if (formula instanceof ImpliesFormula) {
            ImpliesFormula impliesFormula = (ImpliesFormula) formula;
            List<Formula> list = new ArrayList<Formula>();
            list.add(impliesFormula.getLeftSide().negationNormalForm());
            list.add((new NotFormula(impliesFormula.getRightSide()))
                    .negationNormalForm());
            return new AndFormula(list);
        }

        // MacroInstance
        if (formula instanceof PropositionalFunctionMacroInstance) {
            PropositionalFunctionMacro negatedMacro = ((PropositionalFunctionMacroInstance) formula)
                    .getMacro().negatedMacro();
            Map<Token, Term> paramMap = new HashMap<Token, Term>(
                    ((PropositionalFunctionMacroInstance) formula)
                            .getParamMap());
            return new PropositionalFunctionMacroInstance(negatedMacro,
                    paramMap);
        }

        // PropositionalITE
        if (formula instanceof PropositionalIte) {
            PropositionalIte iteFormula = (PropositionalIte) formula;
            Formula thenBranch = (new NotFormula(iteFormula.getThenBranch()))
                    .negationNormalForm();
            Formula elseBranch = (new NotFormula(iteFormula.getElseBranch()))
                    .negationNormalForm();
            return new PropositionalIte(iteFormula.getCondition()
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
        if (!(obj instanceof NotFormula))
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
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(java.util.Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, Term> paramMap) {
        return new NotFormula(formula.substituteFormula(paramMap));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        if (formula instanceof ArrayEq)
            formula = ((ArrayEq) formula).toArrayProperties();
        else
            formula.removeArrayEqualities();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        if (formula instanceof ArrayProperty)
            formula = ((ArrayProperty) formula).toFiniteConjunction(indexSet);
        else
            formula.arrayPropertiesToFiniteConjunctions(indexSet);
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
        formula = formula.simplify();

        if (formula instanceof PropositionalConstant)
            return new PropositionalConstant(
                    !((PropositionalConstant) formula).getValue());

        if (formula instanceof NotFormula)
            return ((NotFormula) formula).formula;

        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        return new NotFormula(formula.flatten());
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
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        formula.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        formula.arrayReadsToUninterpretedFunctions(noDependenceVars);
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
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        formula.substituteUninterpretedFunction(oldFunction, newFunction);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public void makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        formula.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        return new NotFormula(
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
	
    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformFormulaToConsequentsFormula(at.iaik.suraq.smtlib.formula.Formula)
     */
	@Override
	public Formula transformToConsequentsForm(Formula formula) {
		return transformToConsequentsForm(formula, false, true);
	}
	
    /** 
     * Transforms formula to formula for consequents.
     * Formulas for consequents should have the following structure:
     *  		- each atom is either a positive equality of two terms, a propositional variable,
     *  			or an uninterpreted predicate
     *   		- each literal is either an atom or a negation of an atom
     *   		- formula is always an or formula which consists of at least one literal 
     *   
     * @param fomrula
     * 			to be transformed into a consequents formula 
     * @param notFlag
     * 			indicates if number of not operations occurred so far is even or odd 
     * 			(notFlag=true equates to odd number)
     * @param firstLevel
     * 			indicates if function call appeared in the first recursion step
     * @return the new transformed formula is possible, if not null
     *  	 
     */
	
	@Override
    public Formula transformToConsequentsForm(Formula formula, boolean notFlag, boolean firstLevel) {

		Formula notFormula;
		
		if (isAtom(this.formula)){
			if (notFlag == false)
				notFormula = new NotFormula (this.formula.transformToConsequentsForm(formula, !notFlag, false));
			else  //odd number of NOT operators equates no NOT operator
				notFormula = this.formula.transformToConsequentsForm(formula, !notFlag, false); 
		}
		else if (this.formula instanceof NotFormula) {
			notFormula = this.formula.transformToConsequentsForm(formula, !notFlag, false);
		}		
		else if (this.formula instanceof AndFormula) {  //is ok, because of deMorgan rule
			notFormula = this.formula.transformToConsequentsForm(formula, !notFlag, false);		
		}
		else 
			throw new RuntimeException(
                    "Unexpected Body: Body of an Not Formula can either be an AND Formula, a NOT Formula or an atom");		
		
        if (firstLevel==true){				

			List<Formula> literals = new ArrayList<Formula>(); 
			literals.add(notFormula);
			Formula orFormula = new OrFormula(literals);
			return	orFormula;	
		}
        return notFormula;

	}

    /** 
     * Checks if a given Formula is an atom in a consequents of a proof
     * An atom is either a <code>EqualityFormula</code>, a <code>PropositionalVariable</code>
     * or a <code>UninterpretedPredicateInstance</code>
     * 
     * @param formula
     * 		formula to check 
     * @return true, iff formula is an atom
     *  	 
     */
	public boolean isAtom(Formula formula){
		if (formula instanceof EqualityFormula)
            return true;
		if (formula instanceof PropositionalVariable)
            return true;		
		if (formula instanceof UninterpretedPredicateInstance)
            return true;		
		return false;
	}

}
