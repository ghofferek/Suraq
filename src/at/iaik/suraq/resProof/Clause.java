/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */
package at.iaik.suraq.resProof;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.TreeSet;

/**
 * Represents a clause in a node of a resolution proof. Clauses are immutable.
 * 
 */
public class Clause implements Iterable<Literal> {

    /**
     * The literals in this clause. This is supposed to be sorted according to
     * the natural order of Literals.
     */
    private final Literal[] literals;

    /**
     * The hashCode.
     */
    private final int hashCode;

    /**
     * 
     * Constructs a new <code>Clause</code> that is empty.
     */
    public Clause() {
        literals = new Literal[0];
        hashCode = 0;
    }

    /**
     * 
     * Constructs a new <code>Clause</code> with the given literals.
     * 
     * @param literal
     */
    public Clause(Collection<Literal> literal) {
        TreeSet<Literal> literalSet = new TreeSet<Literal>();
        literalSet.addAll(literal);
        Literal[] litArray = new Literal[literalSet.size()];
        literals = literalSet.toArray(litArray);
        assert (literalsSorted());
        hashCode = literalSet.hashCode();
    }

    /**
     * 
     * Constructs a new <code>Clause</code>. (Copy constructor)
     * 
     * @param clause
     */
    public Clause(Clause clause) {
        this(Arrays.asList(clause.literals));
    }

    /**
     * 
     * Constructs a new <code>Clause</code> that is the result of resolving the
     * two given collections of literals over the given pivot.
     * 
     * @param clLeft
     * @param clRight
     * @param pivot
     */
    public Clause(Clause clLeft, Clause clRight, int pivot) {
        TreeSet<Literal> literalSet = new TreeSet<Literal>();
        Collections.addAll(literalSet, clLeft.literals);
        literalSet.remove(Literal.create(pivot, true));
        if (literalSet.contains(Literal.create(pivot, false))) {
            Collections.addAll(literalSet, clRight.literals);
        } else {
            Collections.addAll(literalSet, clRight.literals);
            literalSet.remove(Literal.create(pivot, false));
        }
        Literal[] litArray = new Literal[literalSet.size()];
        literals = literalSet.toArray(litArray);
        assert (literalsSorted());
        hashCode = literalSet.hashCode();
    }

    /**
     * Checks if the array of literals is sorted.
     * 
     * @return
     */
    private boolean literalsSorted() {
        for (int count = 1; count < literals.length; count++) {
            if (literals[count - 1].compareTo(literals[count]) >= 0)
                return false;
        }
        return true;
    }

    /**
     * Checks whether the clause contains the literal with the given id and
     * polarity.
     * 
     * @param id
     * @param polarity
     * @return
     */
    public boolean contains(int id, boolean polarity) {
        return contains(Literal.create(id, polarity));
    }

    /**
     * Checks whether the given literal is contained in this clause.
     * 
     * @param literal
     * @return <code>true</code> iff <code>literal</code> is contained in this
     *         clause.
     */
    public boolean contains(Literal literal) {
        return Arrays.binarySearch(literals, literal) >= 0;
    }

    /**
     * 
     * @return <code>true</code> if this clause is empty.
     */
    public boolean isEmpty() {
        return literals.length == 0;
    }

    /**
     * 
     * @return an iterator over the literals of this clause
     */
    @Override
    public Iterator<Literal> iterator() {
        return Arrays.asList(literals).iterator();
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return hashCode;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof Clause))
            return false;
        if (this.hashCode() != obj.hashCode())
            return false;
        if (!Arrays.equals(literals, ((Clause) obj).literals))
            return false;

        return true;
    }
}
