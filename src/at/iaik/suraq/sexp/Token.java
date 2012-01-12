/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.sexp;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.exceptions.NotATokenListException;

/**
 * A class representing a single token
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
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
     * Constructs a new <code>Token</code>.
     * 
     * @param token
     *            the string representation of the token.
     */
    public Token(StringBuffer token) {
        this.token = token.toString();
    }

    /**
     * Constructs a new <code>Token</code>.
     * 
     * @param token
     *            the string representation of the token.
     */
    public Token(StringBuffer token, int lineNumber, int columnNumber) {
        this.token = token.toString();
        this.lineNumber = lineNumber;
        this.columnNumber = columnNumber;
    }

    /**
     * Constructs a new <code>Token</code>, which is a copy of the given one.
     * 
     * @param original
     *            the <code>Token</code> to copy.
     */
    public Token(Token original) {
        this.token = new String(original.token);
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

    /**
     * @see at.iaik.suraq.sexp.SExpression#deepCopy()
     */
    @Override
    public SExpression deepCopy() {
        return new Token(token);
    }

    /**
     * @see at.iaik.suraq.sexp.SExpression#getChildren()
     */
    @Override
    public List<SExpression> getChildren() {
        return null;
    }

    /**
     * @see at.iaik.suraq.sexp.SExpression#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof Token))
            return false;
        return token.equals(((Token) obj).token);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return token.hashCode();
    }

    /**
     * Convenience method to match a token versus a <code>String</code>.
     * 
     * @param string
     *            the <code>String</code> to compare with this token.
     * @return <code>true</code> if this <code>Token</code> matches the given
     *         <code>string</code>, <code>false</code> otherwise
     */
    public boolean equalsString(String string) {
        return token.equals(string);
    }

    /**
     * @see at.iaik.suraq.sexp.SExpression#toTokenList()
     */
    @Override
    public List<Token> toTokenList() throws NotATokenListException {
        List<Token> list = new ArrayList<Token>();
        list.add(this);
        return list;
    }

}
