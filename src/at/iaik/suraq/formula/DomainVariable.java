/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import at.iaik.suraq.sexp.Token;

/**
 * A class representing domain variables.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class DomainVariable extends DomainTerm {
    /**
     * The name of the variable.
     */
    private final String varName;

    /**
     * 
     * Constructs a new <code>DomainVariable</code>.
     * 
     * @param varName
     *            the name of the variable.
     */
    public DomainVariable(String varName) {
        this.varName = varName;
    }

    /**
     * 
     * Constructs a new <code>DomainVariable</code>.
     * 
     * @param name
     *            the <code>Token</code> representing the variable name.
     */
    public DomainVariable(Token name) {
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
        if (!(obj instanceof DomainVariable))
            return false;
        return varName.equals(((DomainVariable) obj).varName);
    }
}
