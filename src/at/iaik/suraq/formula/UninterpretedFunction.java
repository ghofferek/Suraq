/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import at.iaik.suraq.sexp.Token;

/**
 * This class represents uninterpreted functions. It stores the name of the
 * function and the number of parameters. All parameters need to be of sort
 * <code>Value</code>.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class UninterpretedFunction {

    /**
     * The number of parameters.
     */
    private final int numParams;

    /**
     * The name of this function.
     */
    private final Token name;

    /**
     * 
     * Constructs a new <code>UninterpretedFunction</code>.
     * 
     * @param name
     *            the name of the function
     * @param numParams
     *            the number of parameters.
     */
    public UninterpretedFunction(String name, int numParams) {
        this.name = new Token(name);
        this.numParams = numParams;
    }

    /**
     * 
     * Constructs a new <code>UninterpretedFunction</code>.
     * 
     * @param name
     *            the name of the function
     * @param numParams
     *            the number of parameters.
     */
    public UninterpretedFunction(Token name, int numParams) {
        this.name = name;
        this.numParams = numParams;
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
        this.name = (Token) original.name.deepCopy();
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

}
