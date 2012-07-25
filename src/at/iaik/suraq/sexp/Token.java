/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.sexp;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.exceptions.NotATokenListException;
import at.iaik.suraq.util.FormulaCache;

/**
 * A class representing a single token
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
public class Token extends SExpression implements Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = 1428132654399245852L;
    /**
     * The string representation of the token.
     */
    private final String token;

    private final int hashCode;

    /**
     * Constructs a new <code>Token</code>.
     * 
     * @param token
     *            the string representation of the token.
     */
    protected Token(String token) {
        this.token = token;
        hashCode = token.hashCode();
    }    
    public static Token generate(String token)
    {
    	Token t = new Token(token);
    	return FormulaCache.token.put(t);
    }

    /**
     * Constructs a new <code>Token</code>.
     * 
     * @param token
     *            the string representation of the token.
     */
    protected Token(StringBuffer token) {
        this.token = token.toString();
        hashCode = token.hashCode();
    }
    public static Token generate(StringBuffer token)
    {
    	Token t = new Token(token);
    	return FormulaCache.token.put(t);
    }

    /**
     * Constructs a new <code>Token</code>.
     * 
     * @param token
     *            the string representation of the token.
     */
    protected Token(StringBuffer token, int lineNumber, int columnNumber) {
        this.token = token.toString();
        this.lineNumber = lineNumber;
        this.columnNumber = columnNumber;
        hashCode = token.hashCode();
    }
    public static Token generate(StringBuffer token, int lineNumber, int columnNumber)
    {
    	Token t = new Token(token, lineNumber, columnNumber);
    	return FormulaCache.token.put(t);
    }

    /**
     * Constructs a new <code>Token</code>, which is a copy of the given one.
     * 
     * @param original
     *            the <code>Token</code> to copy.
     */
    protected Token(Token original) {
        this.token = new String(original.token);
        hashCode = token.hashCode();
    }
    public static Token generate(Token original)
    {
    	Token t = new Token(original);
    	return FormulaCache.token.put(t);
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
        if (this == obj)
            return true;

        if (!(obj instanceof Token))
            return false;

        if (this.hashCode != ((Token) obj).hashCode)
            return false;

        if (token.length() != ((Token) obj).token.length())
            return false;

        return token.equals(((Token) obj).token);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return hashCode;
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
