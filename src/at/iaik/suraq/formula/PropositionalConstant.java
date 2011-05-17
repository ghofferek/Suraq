/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

/**
 * A formula that consists of a simple propositional constant.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalConstant extends Formula {

    private final boolean constant;

    /**
     * 
     * Constructs a new <code>PropositionalConstant</code>.
     * 
     * @param constant
     *            the value to use.
     */
    public PropositionalConstant(boolean constant) {
        this.constant = constant;
    }

    /**
     * Returns the value of this constant.
     * 
     * @return the value of this constant
     */
    public boolean getValue() {
        return constant;
    }

}
