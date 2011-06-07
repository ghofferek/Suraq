/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Collection;
import java.util.Set;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayRead extends DomainTerm {

    /**
     * The array variable that is read.
     */
    private final ArrayTerm arrayTerm;

    /**
     * The index from which is read.
     */
    private final DomainTerm index;

    /**
     * Constructs a new <code>ArrayRead</code>.
     * 
     * @param arrayTerm
     *            the variable that is read
     * @param index
     *            the index from which is read.
     */
    public ArrayRead(ArrayTerm arrayTerm, DomainTerm index) {
        super();
        this.arrayTerm = arrayTerm;
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
    public ArrayTerm getArrayTerm() {
        return arrayTerm;
    }

    /**
     * @see at.iaik.suraq.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return new ArrayRead((ArrayTerm) arrayTerm.deepTermCopy(),
                (DomainTerm) index.deepTermCopy());
    }

    /**
     * @see at.iaik.suraq.formula.Term#getSetOfArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getSetOfArrayVariables() {
        Set<ArrayVariable> result = arrayTerm.getSetOfArrayVariables();
        result.addAll(index.getSetOfArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getSetOfDomainVariables()
     */
    @Override
    public Set<DomainVariable> getSetOfDomainVariables() {
        Set<DomainVariable> result = arrayTerm.getSetOfDomainVariables();
        result.addAll(index.getSetOfDomainVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getSetOfPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getSetOfPropositionalVariables() {
        Set<PropositionalVariable> result = arrayTerm
                .getSetOfPropositionalVariables();
        result.addAll(index.getSetOfPropositionalVariables());
        return result;
    }
}
