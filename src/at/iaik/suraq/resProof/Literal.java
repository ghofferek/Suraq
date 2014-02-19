/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */
package at.iaik.suraq.resProof;

import java.lang.ref.WeakReference;
import java.util.Map;
import java.util.WeakHashMap;

/**
 * 
 * Represents a literal in a resolution proof. A literal has an integer
 * identifier and a polarity. To save memory, both are stored in one
 * <code>int</code>. The last bit is used to store the polarity.
 * 
 * <code>Literal</code> objects are immutable.
 * 
 */
public class Literal implements Comparable<Literal> {

    /**
     * Stores the unique literal objects.
     */
    private static final Map<Literal, WeakReference<Literal>> uniqueLiterals = new WeakHashMap<Literal, WeakReference<Literal>>();

    /**
     * the internal storage for identifier and polarity
     */
    private final int lit;

    /**
     * 
     * Constructs a new <code>Literal</code>, based on the given
     * <code>lit</code>.
     * 
     * @param lit
     *            the internal <code>lit</code> of another <code>Literal</code>.
     */
    private Literal(int lit) {
        this.lit = lit;
    }

    /**
     * 
     * Constructs a new <code>Literal</code>, based on the given identifier and
     * polarity.
     * 
     * @param id
     * @param polarity
     */
    private Literal(int id, boolean polarity) {
        lit = (id << 1) | (polarity ? 1 : 0);
    }

    /**
     * 
     * Constructs a new <code>Literal</code>, based on the given
     * <code>lit</code>. If the same literal object already exists, the existing
     * reference is returned.
     * 
     * @param lit
     *            the internal <code>lit</code> of another <code>Literal</code>.
     */
    public static Literal create(int lit) {
        Literal newLiteral = new Literal(lit);
        WeakReference<Literal> oldLiteralRef = Literal.uniqueLiterals
                .get(newLiteral);
        if (oldLiteralRef != null) {
            Literal oldLiteral = oldLiteralRef.get();
            if (oldLiteral != null) {
                return oldLiteral;
            }
        }
        Literal.uniqueLiterals.put(newLiteral, new WeakReference<Literal>(
                newLiteral));
        return newLiteral;
    }

    /**
     * 
     * Constructs a new <code>Literal</code>, based on the given identifier and
     * polarity. If the same literal object already exists, the existing
     * reference is returned.
     * 
     * @param id
     * @param polarity
     */
    public static Literal create(int id, boolean polarity) {
        Literal newLiteral = new Literal(id, polarity);
        WeakReference<Literal> oldLiteralRef = Literal.uniqueLiterals
                .get(newLiteral);
        if (oldLiteralRef != null) {
            Literal oldLiteral = oldLiteralRef.get();
            if (oldLiteral != null) {
                return oldLiteral;
            }
        }
        Literal.uniqueLiterals.put(newLiteral, new WeakReference<Literal>(
                newLiteral));
        return newLiteral;
    }

    /**
     * 
     * @return the variable identifier of this literal (disregarding polarity,
     *         i.e., always positive).
     */
    public int id() {
        return lit >> 1;
    }

    /**
     * 
     * @return <code>true</code> iff this literal is positive.
     */
    public boolean isPos() {
        return (lit & 0x1) == 1;
    }

    /**
     * 
     * @return the negated version of this literal.
     */
    public Literal negate() {
        return Literal.create(lit ^ 0x1);
    }

    /**
     * 
     * @return the internal <code>lit</code>.
     */
    public int getLit() {
        return lit;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (this.getClass() != obj.getClass())
            return false;
        return this.lit == ((Literal) obj).lit;
    }

    @Override
    public int hashCode() {
        return lit;
    }

    @Override
    public String toString() {
        if ((lit & 1) == 0)
            return "~" + (lit >> 1);
        else
            return Integer.toString(lit >> 1);
    }

    /**
     * @return the identifying <code>int</code> of this literal, with a sign
     *         signifying the polarity.
     */
    public int signed_var() {
        return (lit >> 1) * ((lit & 0x1) == 1 ? 1 : -1);
    }

    /**
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     */
    @Override
    public int compareTo(Literal other) {
        if (other == null)
            throw new NullPointerException();

        return this.lit - other.lit;
    }

}
