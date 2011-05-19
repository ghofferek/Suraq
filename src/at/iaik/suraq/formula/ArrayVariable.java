/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import at.iaik.suraq.sexp.Token;

/**
 * A class representing an array variable.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayVariable extends ArrayTerm {
    /**
     * The name of the variable.
     */
    private final String varName;

    /**
     * 
     * Constructs a new <code>ArrayVariable</code>.
     * 
     * @param varName
     *            the name of the variable.
     */
    public ArrayVariable(String varName) {
        this.varName = varName;
    }

    /**
     * 
     * Constructs a new <code>ArrayVariable</code>.
     * 
     * @param name
     *            the <code>Token</code> representing the variable name.
     */
    public ArrayVariable(Token name) {
        this.varName = name.toString();
    }

    /**
     * Get the variable name.
     * 
     * @return the <code>varName</code>
     */
    public String getVarName() {
        return varName;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof ArrayVariable))
            return false;
        return varName.equals(((ArrayVariable) obj).varName);
    }
}
