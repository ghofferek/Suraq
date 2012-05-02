/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.sexp.Token;

/**
 * This class represents uninterpreted functions. It stores the name of the
 * function and the number of parameters. All parameters need to be of sort
 * <code>Value</code>. The return type may be <code>Value</code> or
 * <code>Bool</code>.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class UninterpretedFunction {

	 /**
     * The assert-partitions
     */
	protected List<Integer> assertPartitions = new ArrayList<Integer>();
	
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
    public UninterpretedFunction(String name, int numParams, Token type) {
        this.name = new Token(name);
        this.numParams = numParams;
        this.type = type;
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
    public UninterpretedFunction(Token name, int numParams, Token type) {
        this.name = name;
        this.numParams = numParams;
        this.type = type;
    }

    /**
     * 
     * Constructs a new <code>UninterpretedFunction</code> as a deep copy of the
     * given one.
     * 
     * @param original
     *            the object to (deep) copy
     */
    public UninterpretedFunction(UninterpretedFunction original) {
        this.numParams = original.numParams;
        this.name = new Token(original.name);
        this.type = new Token(original.type);
    }

    public UninterpretedFunction(String name, int numParams, Token type,
			int assertPartition) {
    	this.name = new Token(name);
        this.numParams = numParams;
        this.type = type;
    	this.assertPartitions.add(assertPartition);
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
        if (!(obj instanceof UninterpretedFunction))
            return false;
        return ((UninterpretedFunction) obj).name.equals(name)
                && ((UninterpretedFunction) obj).numParams == numParams;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return name.hashCode() + numParams;
    }
    
    /**
     * @see java.lang.Object#toString()
     */
    @Override    
    public String toString(){
    	return this.name.toString();
    }
    
    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    public List<Integer> getAssertPartition(){
    	return new ArrayList<Integer>(this.assertPartitions);
    }

}
