/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.sexp;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.exceptions.NotATokenListException;
import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.parser.SExpParser;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;

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
        if (child == null)
            throw new RuntimeException(
                    "empty child found! null is not allowed!");
        this.children.add(child);
    }

    /**
     * Convenience method to construct an <code>SExpression</code> with exactly
     * two children. Constructs a new <code>SExpression</code>.
     * 
     * @param first
     *            the first child
     * @param second
     *            the second child
     */
    public SExpression(SExpression first, SExpression second) {
        this.children = new ArrayList<SExpression>();
        if (first == null)
            throw new RuntimeException(
                    "empty child found! null is not allowed!");
        if (second == null)
            throw new RuntimeException(
                    "empty child found! null is not allowed!");
        this.children.add(first);
        this.children.add(second);
    }

    /**
     * Convenience method to construct an <code>SExpression</code> with exactly
     * three children. Constructs a new <code>SExpression</code>.
     * 
     * @param first
     *            the first child
     * @param second
     *            the second child
     * @param third
     *            the third child
     */
    public SExpression(SExpression first, SExpression second, SExpression third) {
        this.children = new ArrayList<SExpression>();
        if (first == null)
            throw new RuntimeException(
                    "empty child found! null is not allowed!");
        if (second == null)
            throw new RuntimeException(
                    "empty child found! null is not allowed!");
        if (third == null)
            throw new RuntimeException(
                    "empty child found! null is not allowed!");
        this.children.add(first);
        this.children.add(second);
        this.children.add(third);
    }

    /**
     * 
     * Constructs a new <code>SExpression</code> by parsing the given String. If
     * <code>string</code> contains a single expression (or token), then this
     * single expression (token) is returned. If it contains a sequence of
     * expressions (tokens) then this sequence will be embedded into a root
     * expression.
     * 
     * @param string
     *            the <code>String</code> to be parsed.
     * @return the parsed expression, or <code>null</code> if parsing was
     *         unsuccessful;
     */
    public static SExpression fromString(String string) {
        SExpParser parser = new SExpParser(string);
        try {
            parser.parse();
        } catch (ParseError exc) {
            return null;
        }
        if (!parser.wasParsingSuccessfull())
            return null;
        List<SExpression> children = parser.getRootExpr().getChildren();
        if (children.size() == 1)
            return children.get(0);
        else
            return new SExpression(children);
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
        if (sexp == null)
            throw new RuntimeException(
                    "empty child found! null is not allowed!");
        children.add(sexp);
    }

    /**
     * Replaces the given s-expression in the children of this one, at the
     * specified position.
     * 
     * @param sexp
     *            the new child to add.
     * @param position
     *            the position of the child to replace.
     */
    public void replaceChild(SExpression sexp, int position) {
        if (sexp == null)
            throw new RuntimeException(
                    "empty child found! null is not allowed!");
        children.add(position, sexp);
        children.remove(position + 1);
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
        if (sexp == null)
            throw new RuntimeException(
                    "empty child found! null is not allowed!");
        children.add(position, sexp);
    }

    /**
     * Removes the child with the specified index.
     * 
     * @param index
     *            index of the element to remove.
     */
    public void removeChild(int index) {
        children.remove(index);
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
            return "()";

        if (size() == 1)
            return "(" + children.get(0).toString() + ")";

        StringBuffer buffer = new StringBuffer();
        buffer.append("(\n  ");
        for (SExpression child : children) {
            buffer.append((child instanceof Token ? child.toString() + "\n"
                    : child.toString() + ((child.size() > 1) ? "" : "\n"))
                    .replace("\n", "\n  "));
        }
        if (buffer.substring(buffer.length() - 2).equals("  "))
            buffer = buffer.delete(buffer.length() - 2, buffer.length());
        else
            buffer.append("\n");
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
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        int code = 0;
        for (int count = 0; count < children.size(); count++) {
            code = code ^ children.get(count).hashCode();
        }
        return code;
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

    /**
     * Creates an SExpression for a function declaration. Produces something of
     * the form <code>(declare-fun name () type)</code>. If
     * <code>numParams > 0</code> the corresponding number if <code>Value</code>
     * parameters will be added. E.g. for <code>numParams==2</code>:
     * <code>(declare-fun name (Value Value) type)</code>.
     * 
     * @param name
     *            the name of the function
     * @param type
     *            the type of the function
     * @param numParams
     *            the number of parameters (all of type <code>Value</code>).
     *            Negative values will be treated as zero.
     * @return an <code>SExpression</code> declaring the specified function.
     */
    public static SExpression makeDeclareFun(Token name, SExpression type,
            int numParams) {

        if (type == null)
            throw new RuntimeException("null 'type' is not allowed!");

        SExpression result = new SExpression();
        result.addChild(SExpressionConstants.DECLARE_FUN);
        result.addChild(name);
        if (numParams > 0) {
            SExpression params = new SExpression();
            for (int count = 0; count < numParams; count++)
                params.addChild(SExpressionConstants.VALUE_TYPE);
            result.addChild(params);
        } else
            result.addChild(SExpressionConstants.EMPTY);
        result.addChild(type);
        return result;
    }

    /**
     * Creates an SExpression for an assert statement for a control signal. Is
     * used to check if formula is a valid implementation for a control signal.
     * 
     * @param controlSignal
     *            the control signal for which a assert statement is generated
     * @param controlFormula
     *            the formula that implements the signal
     * @return an <code>SExpression</code> for the assert statement
     */
    public static SExpression makeControlAssert(
            PropositionalVariable controlSignal, Formula controlFormula) {

        SExpression eqFormulaExp = new SExpression(SExpressionConstants.EQUAL,
                fromString(controlSignal.toString()),
                fromString(controlFormula.toString()));

        SExpression result = new SExpression(SExpressionConstants.ASSERT,
                eqFormulaExp);

        return result;
    }

    /**
     * Checks an expression to be a valid proof type.
     * 
     * @param expr
     *            the expression to check
     * @return an <code>Boolean</code> value declaring iff expr is a valid proof
     *         type
     */

    public static Boolean isValidProofType(Token expr) {

        for (SExpression proofType : SExpressionConstants.PROOF_TYPES) {
            if (proofType.equals(expr))
                return true;
        }
        return false;
    }

    /**
     * Checks an expression to be a valid formula type.
     * 
     * @param expr
     *            the expression to check
     * @return an <code>Boolean</code> value declaring iff expr is a valid
     *         formula type
     */

    public static Boolean isValidFormulaType(Token expr) {
        if (SExpressionConstants.AND.equals(expr))
            return true;
        if (SExpressionConstants.EQUAL.equals(expr))
            return true;
        if (SExpressionConstants.IMPLIES.equals(expr)
                || SExpressionConstants.IMPLIES_ALT.equals(expr))
            return true;
        if (SExpressionConstants.NOT.equals(expr))
            return true;
        if (SExpressionConstants.OR.equals(expr))
            return true;
        if (SExpressionConstants.XOR.equals(expr))
            return true;
        if (SExpressionConstants.ITE.equals(expr))
            return true;
        return false;
    }

}
