/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.sexp;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 *         This class represents s-expressions. It consists of a list of
 *         subexpressions.
 */
public class SExpression {

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
    public SExpression(List<SExpression> children) {
        this.children = new ArrayList<SExpression>();
        this.children.addAll(children);
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
        buffer.append("(\n");
        for (SExpression child : children) {
            buffer.append(child.toString().replace("\n", "\n  "));
        }
        buffer.append(")");
        return buffer.toString();
    }
}
