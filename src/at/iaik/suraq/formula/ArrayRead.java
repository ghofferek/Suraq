/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Collection;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayRead extends DomainTerm {

    /**
     * The array variable that is read.
     */
    private final ArrayVariable variable;

    /**
     * The index from which is read.
     */
    private final DomainTerm index;

    /**
     * Constructs a new <code>ArrayRead</code>.
     * 
     * @param variable
     *            the variable that is read
     * @param index
     *            the index from which is read.
     */
    public ArrayRead(ArrayVariable variable, DomainTerm index) {
        super();
        this.variable = variable;
        this.index = index;
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
    public DomainTerm getIndex() {
        return index;
    }

    /**
     * Returns the array variable from which is read.
     * 
     * @return the array variable from which is read.
     */
    public ArrayVariable getVariable() {
        return variable;
    }
}
