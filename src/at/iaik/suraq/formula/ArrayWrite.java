/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Set;

/**
 * An array write expression.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayWrite extends ArrayTerm {

    /**
     * The array to which this expression writes.
     */
    private final ArrayTerm arrayTerm;

    /**
     * The index to which this expression writes.
     */
    private final DomainTerm indexTerm;

    /**
     * The value that is written.
     */
    private final DomainTerm valueTerm;

    /**
     * Constructs a new <code>ArrayWrite</code>.
     * 
     * @param arrayTerm
     *            the array to which is written.
     * @param indexTerm
     *            the index to which is written.
     * @param valueTerm
     *            the value being written.
     */
    public ArrayWrite(ArrayTerm arrayTerm, DomainTerm indexTerm,
            DomainTerm valueTerm) {
        this.arrayTerm = arrayTerm;
        this.indexTerm = indexTerm;
        this.valueTerm = valueTerm;
    }

    /**
     * Returns the array to which is written.
     * 
     * @return the <code>arrayTerm</code>
     */
    public ArrayTerm getArrayTerm() {
        return arrayTerm;
    }

    /**
     * Returns the index to which is written.
     * 
     * @return the <code>indexTerm</code>
     */
    public DomainTerm getIndexTerm() {
        return indexTerm;
    }

    /**
     * Returns the value being written.
     * 
     * @return the <code>valueTerm</code>
     */
    public DomainTerm getValueTerm() {
        return valueTerm;
    }

    /**
     * @see at.iaik.suraq.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return new ArrayWrite((ArrayTerm) arrayTerm.deepTermCopy(),
                (DomainTerm) indexTerm.deepTermCopy(),
                (DomainTerm) valueTerm.deepTermCopy());
    }

    /**
     * @see at.iaik.suraq.formula.Term#getSetOfArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getSetOfArrayVariables() {
        Set<ArrayVariable> result = arrayTerm.getSetOfArrayVariables();
        result.addAll(indexTerm.getSetOfArrayVariables());
        result.addAll(valueTerm.getSetOfArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getSetOfDomainVariables()
     */
    @Override
    public Set<DomainVariable> getSetOfDomainVariables() {
        Set<DomainVariable> result = arrayTerm.getSetOfDomainVariables();
        result.addAll(indexTerm.getSetOfDomainVariables());
        result.addAll(valueTerm.getSetOfDomainVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getSetOfPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getSetOfPropositionalVariables() {
        Set<PropositionalVariable> result = arrayTerm
                .getSetOfPropositionalVariables();
        result.addAll(indexTerm.getSetOfPropositionalVariables());
        result.addAll(valueTerm.getSetOfPropositionalVariables());
        return result;
    }
}
