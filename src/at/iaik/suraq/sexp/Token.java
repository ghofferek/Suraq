/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.sexp;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at> A class representing a
 *         single token
 */
public class Token extends SExpression {

    /**
     * The string representation of the token.
     */
    private final String token;

    /**
     * Constructs a new <code>Token</code>.
     * 
     * @param token
     *            the string representation of the token.
     */
    public Token(String token) {
        this.token = token;
    }

    /**
     * @see at.iaik.suraq.sexp.SExpression#size()
     */
    @Override
    public int size() {
        return 1;
    }

    /**
     * @see at.iaik.suraq.sexp.SExpression#isEmpty()
     */
    @Override
    public boolean isEmpty() {
        return false;
    }

    /**
     * @see at.iaik.suraq.sexp.SExpression#addChild(at.iaik.suraq.sexp.SExpression)
     */
    @Override
    public void addChild(SExpression sexp) {
        throw new UnsupportedOperationException(
                "Cannot add a child to a token!");
    }

    /**
     * @see at.iaik.suraq.sexp.SExpression#addChild(at.iaik.suraq.sexp.SExpression,
     *      int)
     */
    @Override
    public void addChild(SExpression sexp, int position) {
        throw new UnsupportedOperationException(
                "Cannot add a child to a token!");
    }

    /**
     * @see at.iaik.suraq.sexp.SExpression#toString()
     */
    @Override
    public String toString() {
        return token;
    }

}
