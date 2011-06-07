/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import at.iaik.suraq.sexp.Token;

/**
 * A class for formulas that consist just of one propositional variable.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalVariable extends PropositionalTerm {

    /**
     * The name of the variable.
     */
    private final String varName;

    /**
     * 
     * Constructs a new <code>PropositionalVariable</code>.
     * 
     * @param varName
     *            the name of the variable.
     */
    public PropositionalVariable(String varName) {
        this.varName = varName;
    }

    /**
     * 
     * Constructs a new <code>PropositionalVariable</code>.
     * 
     * @param name
     *            the <code>Token</code> representing the variable name.
     */
    public PropositionalVariable(Token name) {
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
        if (!(obj instanceof PropositionalVariable))
            return false;
        return varName.equals(((PropositionalVariable) obj).varName);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return varName.hashCode();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        // TODO Auto-generated method stub
        return null;
    }

    /**
     * @see at.iaik.suraq.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return new PropositionalVariable(new String(varName));
    }
}
