/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.exceptions.WrongNumberOfParametersException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.util.Util;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayRead extends DomainTerm {

    /**
     * The array variable that is read.
     */
    private ArrayTerm arrayTerm;

    /**
     * The index from which is read.
     */
    private final DomainTerm indexTerm;

    /**
     * Constructs a new <code>ArrayRead</code>.
     * 
     * @param arrayTerm
     *            the variable that is read
     * @param index
     *            the index from which is read.
     */
    public ArrayRead(ArrayTerm arrayTerm, DomainTerm index) {
        super();
        this.arrayTerm = arrayTerm;
        this.indexTerm = index;
    }

    /**
     * @see at.iaik.suraq.formula.DomainTerm#isEvar(java.util.Collection)
     */
    @Override
    public boolean isEvar(Collection<DomainVariable> uVars) {
        // not applicable for ArrayRead.
        return false;
    }

    /**
     * Returns the index from which is read.
     * 
     * @return the index from which is read.
     */
    public DomainTerm getIndexTerm() {
        return indexTerm;
    }

    /**
     * Returns the array variable from which is read.
     * 
     * @return the array variable from which is read.
     */
    public ArrayTerm getArrayTerm() {
        return arrayTerm;
    }

    /**
     * @see at.iaik.suraq.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return new ArrayRead((ArrayTerm) arrayTerm.deepTermCopy(),
                (DomainTerm) indexTerm.deepTermCopy());
    }

    /**
     * @see at.iaik.suraq.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> result = arrayTerm.getArrayVariables();
        result.addAll(indexTerm.getArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> result = arrayTerm.getDomainVariables();
        result.addAll(indexTerm.getDomainVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> result = arrayTerm
                .getPropositionalVariables();
        result.addAll(indexTerm.getPropositionalVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = arrayTerm.getFunctionMacroNames();
        result.addAll(indexTerm.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = arrayTerm.getFunctionMacros();
        result.addAll(indexTerm.getFunctionMacros());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = arrayTerm.getUninterpretedFunctionNames();
        result.addAll(indexTerm.getUninterpretedFunctionNames());
        return result;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof ArrayRead))
            return false;
        return arrayTerm.equals(((ArrayRead) obj).arrayTerm)
                && indexTerm.equals(((ArrayRead) obj).indexTerm);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return arrayTerm.hashCode() ^ indexTerm.hashCode();
    }

    /**
     * @see at.iaik.suraq.formula.Term#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        if (!(arrayTerm instanceof ArrayVariable))
            throw new SuraqException(
                    "Encountered array-read from non-variable array term while computing index set.");
        Set<DomainTerm> result = new HashSet<DomainTerm>();
        result.add(indexTerm);
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#substituteTerm(java.util.Map)
     */
    @Override
    public Term substituteTerm(Map<Token, Term> paramMap) {
        return new ArrayRead((ArrayTerm) arrayTerm.substituteTerm(paramMap),
                (DomainTerm) indexTerm.substituteTerm(paramMap));
    }

    /**
     * @see at.iaik.suraq.formula.Term#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        SExpression[] expr = new SExpression[3];
        expr[0] = SExpressionConstants.SELECT;
        expr[1] = arrayTerm.toSmtlibV2();
        expr[2] = indexTerm.toSmtlibV2();
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.formula.Term#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        arrayTerm.arrayPropertiesToFiniteConjunctions(indexSet);
        indexTerm.arrayPropertiesToFiniteConjunctions(indexSet);
    }

    /**
     * @see at.iaik.suraq.formula.Term#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        arrayTerm.removeArrayEqualities();
        indexTerm.removeArrayEqualities();
    }

    /**
     * @see at.iaik.suraq.formula.Term#removeArrayWrites(at.iaik.suraq.formula.Formula)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        if (arrayTerm instanceof ArrayWrite)
            arrayTerm = ((ArrayWrite) arrayTerm).applyWriteAxiom(
                    topLevelFormula, constraints, noDependenceVars);
        else
            arrayTerm.removeArrayWrites(topLevelFormula, constraints,
                    noDependenceVars);

        indexTerm.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);
    }

    /**
     * Returns an <code>UninterpretedFunctionInstance</code> that is
     * "equivalent" to this <code>ArrayRead</code>.
     * 
     * @return an <code>UninterpretedFunctionInstance</code> that is
     *         "equivalent" to this <code>ArrayRead</code>.
     */
    public UninterpretedFunctionInstance toUninterpretedFunctionInstance(
            Set<Token> noDependenceVars) {
        try {
            String functionName = arrayTerm.toSmtlibV2().toString()
                    .replaceAll("\\W", "");

            DomainTerm term = indexTerm;

            if (term instanceof ArrayRead)
                term = ((ArrayRead) term)
                        .toUninterpretedFunctionInstance(noDependenceVars);
            else
                term.arrayReadsToUninterpretedFunctions(noDependenceVars);

            // Check if the arrayTerm contained any noDependenceVars.
            // This is conservative and might not be complete (i.e., may
            // result unnecessary unrealizability), but
            // in practice, array reads should only occur on primitive
            // array expressions, so this should not be a "real" problem.
            if (Util.termContainsAny(arrayTerm, noDependenceVars))
                noDependenceVars.add(new Token(functionName));

            return new UninterpretedFunctionInstance(new UninterpretedFunction(
                    functionName, 1, SExpressionConstants.VALUE_TYPE), term);
        } catch (WrongNumberOfParametersException exc) {
            throw new RuntimeException(
                    "Could not replace array-reads with uninterpreted functions",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        throw new RuntimeException(
                "arrayReadsToUninterpretedFunctions cannot be called on an ArrayWrite.\nUse toUninterpretedFunctionInstance instead.");
    }

    /**
     * @see at.iaik.suraq.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        Set<UninterpretedFunction> result = arrayTerm
                .getUninterpretedFunctions();
        result.addAll(indexTerm.getUninterpretedFunctions());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.formula.UninterpretedFunction)
     */
    @Override
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        arrayTerm.substituteUninterpretedFunction(oldFunction, newFunction);
        indexTerm.substituteUninterpretedFunction(oldFunction, newFunction);
    }

    /**
     * @see at.iaik.suraq.formula.Term#flatten()
     */
    @Override
    public Term flatten() {
        return new ArrayRead((ArrayTerm) arrayTerm.flatten(),
                (DomainTerm) indexTerm.flatten());
    }
}
