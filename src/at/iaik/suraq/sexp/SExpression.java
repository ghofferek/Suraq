/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.sexp;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.exceptions.NotATokenListException;

/**
 * This class represents s-expressions. It consists of a list of subexpressions.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class SExpression {

    /**
     * the line number in the source file corresponding to this expression
     */
    protected int lineNumber = -1;

    /**
     * the column number in the source file corresponding to this expression
     */
    protected int columnNumber = -1;

    /**
     * The children of this (non-Token) S-expression.
     */
    private List<SExpression> children;

    /**
     * Constructs a new <code>SExpression</code>.
     * 
     * @param children
     *            the subexpressions.
     */
    public SExpression(List<? extends SExpression> children) {
        this.children = new ArrayList<SExpression>();
        this.children.addAll(children);
    }

    /**
     * Constructs a new <code>SExpression</code>.
     * 
     * @param children
     *            the subexpressions.
     */
    public SExpression(SExpression[] children) {
        this.children = new ArrayList<SExpression>();
        for (SExpression child : children)
            this.children.add(child);
    }

    /**
     * Constructs a new, empty <code>SExpression</code>.
     */
    public SExpression() {
        this.children = new ArrayList<SExpression>();
    }

    /**
     * Constructs a new <code>SExpression</code>, with only one child.
     * 
     * @param child
     *            the only child of this s-expression.
     */
    public SExpression(SExpression child) {
        this.children = new ArrayList<SExpression>();
        this.children.add(child);
    }

    /**
     * @return the size of this s-expression, i.e., the number of children. 0,
     *         if empty.
     */
    public int size() {
        return children.size();
    }

    /**
     * @return <code>true</code> if this s-expression is empty,
     *         <code>false</code> otherwise.
     */
    public boolean isEmpty() {
        return (children.size() == 0);
    }

    /**
     * Adds the given s-expression to the end of the list of children of this
     * one.
     * 
     * @param sexp
     *            the new child to add
     */
    public void addChild(SExpression sexp) {
        children.add(sexp);
    }

    /**
     * Adds the given s-expression to the children of this one, at the specified
     * position.
     * 
     * @param sexp
     *            the new child to add.
     * @param position
     *            the position of the new child.
     */
    public void addChild(SExpression sexp, int position) {
        children.add(position, sexp);
    }

    /**
     * Returns the list of children. This is the live list, not a copy.
     * 
     * @return the list of children (not a copy).
     */
    public List<SExpression> getChildren() {
        return children;
    }

    /**
     * Converts this s-expression into a list of <code>Token</code>s. Only
     * direct children will be considered. If this expression is empty, an empty
     * list will be returned. If one or more children are not <code>Token</code>
     * s, an exception is thrown.
     * 
     * @return A list of all <code>Token</code>s that are (direct) children of
     *         this expression.
     * @throws NotATokenListException
     *             if one or more children are not <code>Token</code>s.
     */
    public List<Token> toTokenList() throws NotATokenListException {
        List<Token> list = new ArrayList<Token>();
        if (isEmpty())
            return list;
        assert (children != null);

        for (int count = 0; count < children.size(); count++) {
            if (!(children.get(count) instanceof Token))
                throw new NotATokenListException(children.get(count).toString()
                        + " is not a Token!");
            else
                list.add((Token) children.get(count));
        }
        return list;
    }

    /**
     * Returns a pretty-printed string representation of this s-expression.
     * 
     * @return a pretty-printed string representation of this s-expression.
     */
    @Override
    public String toString() {
        if (isEmpty())
            return "( )";

        if (size() == 1)
            return "(" + children.get(0).toString() + ")";

        StringBuffer buffer = new StringBuffer();
        buffer.append("(\n  ");
        for (SExpression child : children) {
            buffer.append(child.toString().replace("\n", "\n  "));
        }
        buffer = buffer.delete(buffer.length() - 2, buffer.length());
        buffer.append(")\n");
        return buffer.toString();
    }

    /**
     * Recursively copies this s-expression.
     * 
     * @return a deep copy of this s-expression
     */
    public SExpression deepCopy() {
        SExpression copy = new SExpression();
        for (SExpression child : children) {
            copy.addChild(child.deepCopy());
        }
        return copy;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        boolean result = true;

        if (!(obj instanceof SExpression))
            return false;

        SExpression other = ((SExpression) obj);
        if (children.size() != other.children.size())
            return false;

        for (int count = 0; count < children.size(); count++)
            result = result
                    && children.get(count).equals(other.children.get(count));

        return result;
    }

    /**
     * @return the <code>lineNumber</code>
     */
    public int getLineNumber() {
        return lineNumber;
    }

    /**
     * @param <code>lineNumber</code> the new value for <code>lineNumber</code>
     */
    public void setLineNumber(int lineNumber) {
        this.lineNumber = lineNumber;
    }

    /**
     * @return the <code>columnNumber</code>
     */
    public int getColumnNumber() {
        return columnNumber;
    }

    /**
     * @param <code>columnNumber</code> the new value for
     *        <code>columnNumber</code>
     */
    public void setColumnNumber(int columnNumber) {
        this.columnNumber = columnNumber;
    }

}
