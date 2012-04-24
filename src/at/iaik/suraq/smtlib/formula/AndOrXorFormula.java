/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.lang.reflect.Constructor;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * A common superclass for And- Or- and Xor-formulas to avoid code redundancy.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class AndOrXorFormula extends BooleanCombinationFormula {
    /**
     * The list of sub-formulas.
     */
    protected final List<Formula> formulas;

    /**
     * 
     * Constructs a new <code>AndOrXorFormula</code>. Initializes the list of
     * subformulas.
     * 
     * @param formulas
     *            the list of subformulas.
     */
    protected AndOrXorFormula(Collection<? extends Formula> formulas) {
        this.formulas = new ArrayList<Formula>();
        this.formulas.addAll(formulas);
        if (formulas.size() < 1)
            this.formulas.add(new PropositionalConstant(true));
    }

    /**
     * Creates a new <code>AndOrXorFormula</code> which is of the same type as
     * <code>this</code> object and has the given subformulas.
     * 
     * @param formulas
     *            the subformulas
     * @return a new <code>AndOrXorFormula</code> with the same type as
     *         <code>this</code>.
     */
    protected AndOrXorFormula create(Collection<? extends Formula> formulas) {
        Class<? extends AndOrXorFormula> myClass = this.getClass();
        // Class<?> listClass = formulas.getClass();
        AndOrXorFormula instance = null;
        try {
            Constructor<?>[] constructors = myClass.getDeclaredConstructors();
            if (constructors.length == 0)
                throw new RuntimeException("No constructors found.");
            for (Constructor<?> constructor : constructors) {
                Class<?>[] parameters = constructor.getParameterTypes();
                if (parameters.length != 1)
                    continue;
                if (!(parameters[0].isInstance(formulas)))
                    continue;
                instance = (AndOrXorFormula) constructor.newInstance(formulas);
            }
            if (instance == null)
                throw new RuntimeException();
            return instance;
        } catch (Throwable exc) {
            throw new RuntimeException("Unable to create AndOrXorFormula", exc);
        }
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> variables = new HashSet<ArrayVariable>();
        for (Formula formula : formulas)
            variables.addAll(formula.getArrayVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> variables = new HashSet<DomainVariable>();
        for (Formula formula : formulas)
            variables.addAll(formula.getDomainVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> variables = new HashSet<PropositionalVariable>();
        for (Formula formula : formulas)
            variables.addAll(formula.getPropositionalVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.BooleanCombinationFormula#getSubFormulas()
     */
    @Override
    public Collection<Formula> getSubFormulas() {
        return new ArrayList<Formula>(formulas);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        List<Formula> subformulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            subformulas.add(formula.deepFormulaCopy());
        return create(subformulas);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        List<Formula> nnfFormulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            nnfFormulas.add(formula.negationNormalForm());

        return create(nnfFormulas);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> functionNames = new HashSet<String>();
        for (Formula formula : formulas)
            functionNames.addAll(formula.getUninterpretedFunctionNames());
        return functionNames;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> macroNames = new HashSet<String>();
        for (Formula formula : formulas)
            macroNames.addAll(formula.getFunctionMacroNames());
        return macroNames;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> macros = new HashSet<FunctionMacro>();
        for (Formula formula : formulas)
            macros.addAll(formula.getFunctionMacros());
        return macros;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> indexSet = new HashSet<DomainTerm>();
        for (Formula formula : formulas)
            indexSet.addAll(formula.getIndexSet());
        return indexSet;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(this.getClass().isInstance(obj)))
            return false;
        if (!((AndOrXorFormula) obj).formulas.equals(formulas))
            return false;
        return true;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return formulas.hashCode();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#substituteFormula(java.util.Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, Term> paramMap) {
        List<Formula> convertedFormulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            convertedFormulas.add(formula.substituteFormula(paramMap));

        return create(convertedFormulas);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        for (int count = 0; count < formulas.size(); count++) {
            if (formulas.get(count) instanceof ArrayEq)
                formulas.set(count,
                        ((ArrayEq) formulas.get(count)).toArrayProperties());
            else
                formulas.get(count).removeArrayEqualities();
        }
    }

    /**
     * @see at.iaik.suraq.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        for (int count = 0; count < formulas.size(); count++) {
            if (formulas.get(count) instanceof ArrayProperty)
                formulas.set(count, ((ArrayProperty) formulas.get(count))
                        .toFiniteConjunction(indexSet));
            else
                formulas.get(count).arrayPropertiesToFiniteConjunctions(
                        indexSet);
        }
    }

    /**
     * @see at.iaik.suraq.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        // Default, unless a subclass has more clever method
        for (int count = 0; count < formulas.size(); count++)
            formulas.set(count, formulas.get(count).simplify());
        return this;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        List<Formula> flattenedFormulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            flattenedFormulas.add(formula.flatten());

        return create(flattenedFormulas);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        List<SExpression> children = new ArrayList<SExpression>();
        children.add(this.getOperator());
        for (Formula formula : formulas)
            children.add(formula.toSmtlibV2());
        return new SExpression(children);
    }

    /**
     * Returns the token representing the operator (and/or/xor) of this formula.
     * 
     * @return The operator token.
     */
    protected abstract Token getOperator();

    /**
     * @see at.iaik.suraq.formula.Formula#removeArrayWrites(at.iaik.suraq.formula.Formula)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        for (Formula formula : this.getSubFormulas())
            formula.removeArrayWrites(topLevelFormula, constraints,
                    noDependenceVars);

    }

    /**
     * @see at.iaik.suraq.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        for (Formula formula : formulas)
            formula.arrayReadsToUninterpretedFunctions(noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        Set<UninterpretedFunction> functionNames = new HashSet<UninterpretedFunction>();
        for (Formula formula : formulas)
            functionNames.addAll(formula.getUninterpretedFunctions());
        return functionNames;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.formula.UninterpretedFunction)
     */
    @Override
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        for (Formula formula : formulas)
            formula.substituteUninterpretedFunction(oldFunction, newFunction);
    }

    /**
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.toSmtlibV2().toString();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#makeArrayReadsSimple(Formula,
     *      java.util.Set, Set)
     */
    @Override
    public void makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        for (Formula formula : formulas)
            formula.makeArrayReadsSimple(topLevelFormula, constraints,
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
        List<Formula> newFormulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            newFormulas.add(formula
                    .uninterpretedPredicatesToAuxiliaryVariables(
                            topLeveFormula, constraints, noDependenceVars));

        return this.create(newFormulas);
    }

}
