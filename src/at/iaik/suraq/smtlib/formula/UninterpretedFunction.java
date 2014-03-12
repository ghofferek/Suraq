/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.Serializable;
import java.util.Set;
import java.util.TreeSet;

import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;

/**
 * This class represents uninterpreted functions. It stores the name of the
 * function and the number of parameters. All parameters need to be of sort
 * <code>Value</code>. The return type may be <code>Value</code> or
 * <code>Bool</code>.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class UninterpretedFunction implements SMTLibObject, Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = 5520322987626682279L;

    /**
     * The assert-partitions
     */
    protected final int assertPartition;

    /**
     * The number of parameters.
     */
    private final int numParams;

    /**
     * The name of this function.
     */
    private final Token name;

    /**
     * The return type of the function.
     */
    private final Token type;

    private final int hashCode;

    public static UninterpretedFunction create(String name, int numParams,
            Token type) {
        return FormulaCache.uninterpretedFunction
                .put(new UninterpretedFunction(name, numParams, type));
    }

    public static UninterpretedFunction create(Token name, int numParams,
            Token type) {
        return FormulaCache.uninterpretedFunction
                .put(new UninterpretedFunction(name, numParams, type));
    }

    public static UninterpretedFunction create(String name, int numParams,
            Token type, int assertPartition) {
        return FormulaCache.uninterpretedFunction
                .put(new UninterpretedFunction(name, numParams, type,
                        assertPartition));
    }

    public static UninterpretedFunction create(UninterpretedFunction original) {
        return original; // experimental
    }

    /**
     * 
     * Constructs a new <code>UninterpretedFunction</code>.
     * 
     * @param name
     *            the name of the function
     * @param numParams
     *            the number of parameters.
     * @param type
     *            the return type of the function (<code>Value</code> or
     *            <code>Bool</code>).
     */
    private UninterpretedFunction(String name, int numParams, Token type) {
        this.name = Token.generate(name);
        this.numParams = numParams;
        this.type = type;
        assertPartition = Term.GLOBAL_PARTITION;
        this.hashCode = name.hashCode() * 31 * 31 + type.hashCode() * 31
                + numParams;
    }

    /**
     * 
     * Constructs a new <code>UninterpretedFunction</code>.
     * 
     * @param name
     *            the name of the function
     * @param numParams
     *            the number of parameters.
     * @param type
     *            the return type of the function (<code>Value</code> or
     *            <code>Bool</code>).
     */
    private UninterpretedFunction(Token name, int numParams, Token type) {
        this.name = name;
        this.numParams = numParams;
        this.type = type;
        assertPartition = Term.GLOBAL_PARTITION;
        this.hashCode = name.hashCode() * 31 * 31 + type.hashCode() * 31
                + numParams;
    }

    /**
     * 
     * Constructs a new <code>UninterpretedFunction</code> as a deep copy of the
     * given one.
     * 
     * @param original
     *            the object to (deep) copy
     */
    private UninterpretedFunction(UninterpretedFunction original) {
        this.numParams = original.numParams;
        this.name = Token.generate(original.name);
        this.type = Token.generate(original.type);
        this.assertPartition = original.assertPartition;
        this.hashCode = name.hashCode() * 31 * 31 + type.hashCode() * 31
                + numParams;
    }

    /**
     * 
     * Constructs a new <code>UninterpretedFunction</code>.
     * 
     * @param name
     *            the name of the function
     * @param numParams
     *            the number of parameters.
     * @param type
     *            the return type of the function (<code>Value</code> or
     *            <code>Bool</code>).
     * @param assertPartition
     *            the function's assert-partition.
     */
    private UninterpretedFunction(String name, int numParams, Token type,
            int assertPartition) {
        this.name = Token.generate(name);
        this.numParams = numParams;
        this.type = type;
        this.assertPartition = assertPartition;
        this.hashCode = name.hashCode() * 31 * 31 + type.hashCode() * 31
                + numParams;
    }

    /**
     * Returns the number of parameters of this function.
     * 
     * @return the number of parameters.
     */
    public int getNumParams() {
        return numParams;
    }

    /**
     * Returns the name of this function.
     * 
     * @return the <code>name</code>
     */
    public Token getName() {
        return name;
    }

    /**
     * Returns the type of this function.
     * 
     * @return the <code>name</code>
     */
    public Token getType() {
        return type;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof UninterpretedFunction))
            return false;
        if (this.hashCode != ((UninterpretedFunction) obj).hashCode)
            return false;

        if (((UninterpretedFunction) obj).numParams != numParams)
            return false;
        if (!((UninterpretedFunction) obj).name.equals(name))
            return false;
        if (!(this.type.equals(((UninterpretedFunction) obj).type)))
            return false;

        return true;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return hashCode;
    }

    /**
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.name.toString();
    }

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    public Set<Integer> getAssertPartitionFromSymbols() {
        Set<Integer> partitions = new TreeSet<Integer>();
        partitions.add(this.assertPartition);
        return partitions;
    }

    /**
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     */
    @Override
    public int compareTo(SMTLibObject o) {
        return name.compareTo(((UninterpretedFunction) o).name);
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getPartitionsFromSymbols()
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        assert (false); // TODO Auto-generated method stub
        return null;
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        return name;
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getArrayVariables(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getArrayVariables(Set<ArrayVariable> result,
            Set<SMTLibObject> done) {
        return;

    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getDomainVariables()
     */
    @Override
    public void getDomainVariables(Set<DomainVariable> result,
            Set<SMTLibObject> done) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getPropositionalVariables()
     */
    @Override
    public void getPropositionalVariables(Set<PropositionalVariable> result,
            Set<SMTLibObject> done) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getUninterpretedFunctionNames()
     */
    @Override
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done) {
        result.add(name.toString());
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getUninterpretedFunctions(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done) {
        result.add(this);

    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getFunctionMacroNames()
     */
    @Override
    public void getFunctionMacroNames(Set<String> result, Set<SMTLibObject> done) {
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getFunctionMacros()
     */
    @Override
    public void getFunctionMacros(Set<FunctionMacro> result,
            Set<SMTLibObject> done) {
        return;
    }

}
