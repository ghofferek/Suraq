/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */
package at.iaik.suraq.resProof;

import java.util.Collection;
import java.util.Iterator;
import java.util.TreeSet;

public class Clause implements Iterable<Literal> {

    private final TreeSet<Literal> literals = new TreeSet<Literal>();

    /**
     * 
     * Constructs a new <code>Clause</code> that is empty.
     */
    public Clause() {
        super();
    }

    /**
     * 
     * Constructs a new <code>Clause</code> withe the given literals.
     * 
     * @param literal
     */
    public Clause(Collection<Literal> literal) {
        literals.addAll(literal);
    }

    /**
     * 
     * Constructs a new <code>Clause</code>. (Copy constructor)
     * 
     * @param clause
     */
    public Clause(Clause clause) {
        literals.addAll(clause.literals);
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
        literals.addAll(clLeft.literals);
        rmLit(pivot, true);
        if (contains(pivot, false)) {
            literals.addAll(clRight.literals);
        } else {
            literals.addAll(clRight.literals);
            rmLit(pivot, false);
        }
    }

    /**
     * Adds the given literal to this clause.
     * 
     * @param l
     * @return <code>true</code> if the clause did not already contain the
     *         literal.
     */
    public boolean addLit(Literal l) {
        assert (!literals.contains(l.negate()));// "~lit and lit in a clause",
        return literals.add(l);
    }

    /**
     * Removes the given literal from this clause.
     * 
     * @param l
     * @return <code>true</code> if the clause did contain the literal.
     */
    public boolean rmLit(Literal l) {
        return literals.remove(l);
    }

    /**
     * Removes the literal with the given id and polarity from this clause.
     * 
     * @param id
     * @param polarity
     * @return <code>true</code> if the clause contained the literal.
     */
    public boolean rmLit(int id, boolean polarity) {
        return literals.remove(new Literal(id, polarity));
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
        return literals.contains(new Literal(id, polarity));
    }

    /**
     * Checks whether the given literal is contained in this clause.
     * 
     * @param literal
     * @return <code>true</code> iff <code>literal</code> is contained in this
     *         clause.
     */
    public boolean contains(Literal literal) {
        return literals.contains(literal);
    }

    /**
     * Clears this clause. I.e., clears the internal set of literals.
     */
    public void clear() {
        literals.clear();
    }

    /**
     * 
     * @return <code>true</code> if this clause is empty.
     */
    public boolean isEmpty() {
        return literals.isEmpty();
    }

    /**
     * 
     * @return an iterator over the literals of this clause
     */
    @Override
    public Iterator<Literal> iterator() {
        return literals.iterator();
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return literals.hashCode();
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
        return this.literals.equals(((Clause) obj).literals);
    }

}
