/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

/**
 * A class for formulas that consist just of one propositional variable.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalVariable extends Formula {

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
     * Get the variable name.
     * 
     * @return the <code>varName</code>
     */
    public String getVarName() {
        return varName;
    }

}
