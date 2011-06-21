/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.lang.reflect.Constructor;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
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
        return new XorFormula(subformulas);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        List<Formula> nnfFormulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            nnfFormulas.add(formula.negationNormalForm());

        Class<? extends AndOrXorFormula> myClass = this.getClass();
        Class<?> listClass = nnfFormulas.getClass();
        AndOrXorFormula instance;
        try {
            Constructor<? extends AndOrXorFormula> constructor = myClass
                    .getConstructor(listClass);
            instance = constructor.newInstance(nnfFormulas);
            return instance;
        } catch (Throwable exc) {
            throw new RuntimeException(
                    "Unable to create object while putting formula in NNF.",
                    exc);
        }
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
     * @see at.iaik.suraq.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        // TODO Auto-generated method stub
        return null;
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
     * @see at.iaik.suraq.formula.Formula#convertFormulaToCallerScope(java.util.Map)
     */
    @Override
    public Formula convertFormulaToCallerScope(Map<Token, Term> paramMap) {
        List<Formula> convertedFormulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            convertedFormulas
                    .add(formula.convertFormulaToCallerScope(paramMap));

        Class<? extends Formula> thisClass = this.getClass();
        try {
            Constructor<? extends Formula> constructur = thisClass
                    .getConstructor(convertedFormulas.getClass());
            return constructur.newInstance(convertedFormulas);
        } catch (Throwable exc) {
            throw new RuntimeException(
                    "Unexpected exception while converting AndOrXorFormula to caller scope.",
                    exc);
        }
    }

}
