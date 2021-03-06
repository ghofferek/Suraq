/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.exceptions;

import at.iaik.suraq.sexp.SExpression;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ParseError extends SuraqException {

    /**
     * Default value
     */
    private static final long serialVersionUID = 1L;

    /**
     * Line number information about where the parse error occurred. Will be
     * <code>&lt; 0</code> if not available.
     */
    protected final int lineNumber;

    /**
     * Column number information about where the parse error occurred. Will be
     * <code>&lt; 0</code> if not available.
     */
    protected final int columnNumber;

    /**
     * A part of the input on which the parse error occurred. This is supposed
     * to provide context for the user. E.g., this might be one (erroneous)
     * line. Can be empty.
     */
    protected final String context;

    /**
     * The default constructor, providing no particular information.
     */
    public ParseError() {
        lineNumber = -1;
        columnNumber = -1;
        context = "";
    }

    /**
     * Constructs a new <code>ParseError</code>, with the given information.
     * 
     * @param lineNumber
     *            the line number where the error occurred.
     * @param context
     *            the context in which the error occurred.
     * @param message
     *            a detailed error message.
     * @param cause
     *            the cause of the error.
     */
    public ParseError(int lineNumber, String context, String message,
            Throwable cause) {
        super(message, cause);
        this.lineNumber = lineNumber;
        this.context = context;
        this.columnNumber = -1;
    }

    /**
     * Constructs a new <code>ParseError</code>, with the given information.
     * 
     * @param lineNumber
     *            the line number where the error occurred.
     * @param columnNumber
     *            the column number where the error occurred.
     * @param context
     *            the context in which the error occurred.
     * @param message
     *            a detailed error message.
     * @param cause
     *            the cause of the error.
     */
    public ParseError(int lineNumber, int columnNumber, String context,
            String message, Throwable cause) {
        super(message, cause);
        this.lineNumber = lineNumber;
        this.columnNumber = columnNumber;
        this.context = context;
    }

    /**
     * Constructs a new <code>ParseError</code>, with the given information.
     * 
     * @param lineNumber
     *            the line number where the error occurred.
     * @param context
     *            the context in which the error occurred.
     * @param message
     *            a detailed error message.
     */
    public ParseError(int lineNumber, String context, String message) {
        super(message);
        this.lineNumber = lineNumber;
        this.columnNumber = -1;
        this.context = context;
    }

    /**
     * Constructs a new <code>ParseError</code>, with the given information.
     * 
     * @param lineNumber
     *            the line number where the error occurred.
     * @param columnNumber
     *            the column number where the error occurred.
     * @param context
     *            the context in which the error occurred.
     * @param message
     *            a detailed error message.
     */
    public ParseError(int lineNumber, int columnNumber, String context,
            String message) {
        super(message);
        this.lineNumber = lineNumber;
        this.columnNumber = columnNumber;
        this.context = context;
    }

    /**
     * Constructs a new <code>ParseError</code>, with the given information.
     * 
     * @param lineNumber
     *            the line number where the error occurred.
     * @param message
     *            a detailed error message.
     * @param cause
     *            the cause of the error.
     */
    public ParseError(int lineNumber, String message, Throwable cause) {
        super(message, cause);
        this.lineNumber = lineNumber;
        this.context = "";
        this.columnNumber = -1;
    }

    /**
     * Constructs a new <code>ParseError</code>, with the given information.
     * 
     * @param context
     *            the context in which the error occurred.
     * @param message
     *            a detailed error message.
     * @param cause
     *            the cause of the error.
     */
    public ParseError(String context, String message, Throwable cause) {
        super(message, cause);
        this.lineNumber = -1;
        this.columnNumber = -1;
        this.context = context;
    }

    /**
     * Constructs a new <code>ParseError</code>, with the given information.
     * 
     * @param lineNumber
     *            the line number where the error occurred.
     * @param message
     *            a detailed error message.
     */
    public ParseError(int lineNumber, String message) {
        super(message);
        this.lineNumber = lineNumber;
        this.columnNumber = -1;
        this.context = "";
    }

    /**
     * Constructs a new <code>ParseError</code>, with the given information.
     * 
     * @param lineNumber
     *            the line number where the error occurred.
     */
    public ParseError(int lineNumber) {
        this.lineNumber = lineNumber;
        this.columnNumber = -1;
        this.context = "";
    }

    /**
     * Constructs a new <code>ParseError</code>, with the given information.
     * 
     * @param lineNumber
     *            the line number where the error occurred.
     * @param columnNumber
     *            the column number where the error occurred.
     */
    public ParseError(int lineNumber, int columnNumber) {
        this.lineNumber = lineNumber;
        this.columnNumber = columnNumber;
        this.context = "";
    }

    /**
     * Constructs a new <code>ParseError</code>, with the given information.
     * 
     * @param message
     *            A detailed message.
     */
    public ParseError(String message) {
        super(message);
        this.lineNumber = -1;
        this.columnNumber = -1;
        this.context = "";
    }

    /**
     * 
     * Constructs a new <code>ParseError</code>. The line number and column
     * number information, as well as the context is extracted from the given
     * <code>SExpression</code>.
     * 
     * @param expression
     *            the <code>SExpression</code> from which information is
     *            extracted.
     * @param message
     *            a more detailed error message.
     */
    public ParseError(SExpression expression, String message) {
        super(message);
        this.lineNumber = expression.getLineNumber();
        this.columnNumber = expression.getColumnNumber();
        this.context = expression.toString();
    }

    /**
     * 
     * Constructs a new <code>ParseError</code>. The line number and column
     * number information, as well as the context is extracted from the given
     * <code>SExpression</code>.
     * 
     * @param expression
     *            the <code>SExpression</code> from which information is
     *            extracted.
     * @param message
     *            a more detailed error message.
     * @param cause
     *            The cause of this exception
     */
    public ParseError(SExpression expression, String message, Throwable cause) {
        super(message, cause);
        this.lineNumber = expression.getLineNumber();
        this.columnNumber = expression.getColumnNumber();
        this.context = expression.toString();
    }

    /**
     * @return the <code>lineNumber</code>
     */
    public int getLineNumber() {
        return lineNumber;
    }

    /**
     * @return the <code>columnNumber</code>
     */
    public int getColumnNumber() {
        return columnNumber;
    }

    /**
     * @return the <code>context</code>
     */
    public String getContext() {
        return context;
    }
}
