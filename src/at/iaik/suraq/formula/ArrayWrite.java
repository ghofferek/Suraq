/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * An array write expression.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayWrite extends ArrayTerm {

    /**
     * The array to which this expression writes.
     */
    private final ArrayTerm arrayTerm;

    /**
     * The index to which this expression writes.
     */
    private final DomainTerm indexTerm;

    /**
     * The value that is written.
     */
    private final DomainTerm valueTerm;

    /**
     * Constructs a new <code>ArrayWrite</code>.
     * 
     * @param arrayTerm
     *            the array to which is written.
     * @param indexTerm
     *            the index to which is written.
     * @param valueTerm
     *            the value being written.
     */
    public ArrayWrite(ArrayTerm arrayTerm, DomainTerm indexTerm,
            DomainTerm valueTerm) {
        this.arrayTerm = arrayTerm;
        this.indexTerm = indexTerm;
        this.valueTerm = valueTerm;
    }

    /**
     * Returns the array to which is written.
     * 
     * @return the <code>arrayTerm</code>
     */
    public ArrayTerm getArrayTerm() {
        return arrayTerm;
    }

    /**
     * Returns the index to which is written.
     * 
     * @return the <code>indexTerm</code>
     */
    public DomainTerm getIndexTerm() {
        return indexTerm;
    }

    /**
     * Returns the value being written.
     * 
     * @return the <code>valueTerm</code>
     */
    public DomainTerm getValueTerm() {
        return valueTerm;
    }

    /**
     * @see at.iaik.suraq.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return new ArrayWrite((ArrayTerm) arrayTerm.deepTermCopy(),
                (DomainTerm) indexTerm.deepTermCopy(),
                (DomainTerm) valueTerm.deepTermCopy());
    }

    /**
     * @see at.iaik.suraq.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> result = arrayTerm.getArrayVariables();
        result.addAll(indexTerm.getArrayVariables());
        result.addAll(valueTerm.getArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> result = arrayTerm.getDomainVariables();
        result.addAll(indexTerm.getDomainVariables());
        result.addAll(valueTerm.getDomainVariables());
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
        result.addAll(valueTerm.getPropositionalVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = arrayTerm.getFunctionMacroNames();
        result.addAll(indexTerm.getFunctionMacroNames());
        result.addAll(valueTerm.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = arrayTerm.getFunctionMacros();
        result.addAll(indexTerm.getFunctionMacros());
        result.addAll(valueTerm.getFunctionMacros());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = arrayTerm.getUninterpretedFunctionNames();
        result.addAll(indexTerm.getUninterpretedFunctionNames());
        result.addAll(valueTerm.getUninterpretedFunctionNames());
        return result;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof ArrayWrite))
            return false;
        return ((ArrayWrite) obj).arrayTerm.equals(arrayTerm)
                && ((ArrayWrite) obj).indexTerm.equals(indexTerm)
                && ((ArrayWrite) obj).valueTerm.equals(valueTerm);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return arrayTerm.hashCode() ^ indexTerm.hashCode()
                ^ valueTerm.hashCode();
    }

    /**
     * @see at.iaik.suraq.formula.Term#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        throw new SuraqException(
                "Encountered array write while computing index set.");
    }

    /**
     * @see at.iaik.suraq.formula.Term#substituteTerm(java.util.Map)
     */
    @Override
    public Term substituteTerm(Map<Token, Term> paramMap) {
        return new ArrayWrite((ArrayTerm) arrayTerm.substituteTerm(paramMap),
                (DomainTerm) indexTerm.substituteTerm(paramMap),
                (DomainTerm) valueTerm.substituteTerm(paramMap));
    }

    /**
     * @see at.iaik.suraq.formula.Term#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        SExpression[] expr = new SExpression[4];
        expr[0] = SExpressionConstants.SELECT;
        expr[1] = arrayTerm.toSmtlibV2();
        expr[2] = indexTerm.toSmtlibV2();
        expr[3] = valueTerm.toSmtlibV2();
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.formula.Term#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        arrayTerm.arrayPropertiesToFiniteConjunctions(indexSet);
        indexTerm.arrayPropertiesToFiniteConjunctions(indexSet);
        valueTerm.arrayPropertiesToFiniteConjunctions(indexSet);
    }

    /**
     * @see at.iaik.suraq.formula.Term#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        arrayTerm.removeArrayEqualities();
        indexTerm.removeArrayEqualities();
        valueTerm.removeArrayEqualities();
    }

}
