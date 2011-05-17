/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

/**
 * A formula consisting of the equality of two terms.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TermEq extends Formula {

    /**
     * The terms to be compared.
     */
    private final Term[] terms;

    /**
     * 
     * Constructs a new <code>TermEq</code>.
     * 
     * @param term1
     *            the first term of the equality.
     * @param term2
     *            the second term of the equality.
     */
    public TermEq(Term term1, Term term2) {
        terms = new Term[2];
        terms[0] = term1;
        terms[1] = term2;
    }

}
