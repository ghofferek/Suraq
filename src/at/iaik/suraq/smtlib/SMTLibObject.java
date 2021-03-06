package at.iaik.suraq.smtlib;

import java.util.Map;
import java.util.Set;

import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.FunctionMacro;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;

public interface SMTLibObject extends Comparable<SMTLibObject> {

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element. contains -1, iff global elements
     *         are present.
     */
    public Set<Integer> getPartitionsFromSymbols();

    /**
     * Converts this formula into an s-expression compatible with SMTLIBv2. Only
     * the formula itself is converted. No variable/function/macro declarations
     * are included.
     * 
     * @return this formulas as an SMTLIBv2 s-expression.
     */
    public SExpression toSmtlibV2();

    /**
     * Returns a set of all array variables used in this formula.
     * 
     * @return a set of array variables used in this formula.
     */
    public void getArrayVariables(Set<ArrayVariable> result,
            Set<SMTLibObject> done);

    /**
     * Returns a set of all domain variables used in this formula.
     * 
     * @return a set of domain variables used in this formula.
     */
    public void getDomainVariables(Set<DomainVariable> result,
            Set<SMTLibObject> done);

    /**
     * Returns a set of all propositional variables used in this formula.
     * 
     * @return a set of propositional variables used in this formula.
     */
    public void getPropositionalVariables(Set<PropositionalVariable> result,
            Set<SMTLibObject> done);

    /**
     * Returns a set of all uninterpreted function names used in this formula.
     * 
     * @return a set of uninterpreted function names used in this formula.
     */
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done);

    /**
     * Returns a set of all function macro names used in this formula.
     * 
     * @return a set of all function macro names used in this formula.
     */
    public void getFunctionMacroNames(Set<String> result, Set<SMTLibObject> done);

    /**
     * Returns a set of all function macros used in this formula.
     * 
     * @return a set of all function macros used in this formula.
     */
    public void getFunctionMacros(Set<FunctionMacro> result,
            Set<SMTLibObject> done);

    /**
     * Returns all uninterpreted functions used in this formula. Don't confuse
     * with <code>getUninterpretedFunctionNames()</code> which just collects the
     * names of the functions, and not the function objects itself.
     * 
     * @return a set of all uninterpreted functions used in this formula.
     */
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done);

    /**
     * Substitutes the uninterpreted functions according to the given map.
     * Parameters are not changed (except for recursive substitutions).
     * 
     * @param substitutions
     * @param done
     *            DAG-aware cache
     * @return
     */
    public SMTLibObject substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions,
            Map<SMTLibObject, SMTLibObject> done);

    /**
     * Returns a formula where all uninterpreted function instances which match
     * a name in the given set of <code>arrayVars</code> are replaced by
     * corresponding array reads.
     * 
     * @param arrayVarsthe
     *            name of the array vars for matching function names against.
     * @param done
     *            cache to avoid DAG-expansion.
     * @return a formula where array reads have been put back in.
     * 
     */
    public SMTLibObject uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars, Map<SMTLibObject, SMTLibObject> done);

    /**
     * 
     * @return a String representation of this object
     */
    @Override
    public String toString();

    /**
     * @return the unique ID of this object.
     */
    public long getId();
}
