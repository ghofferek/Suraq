/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.exceptions;

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
        this.context = context;
    }

    /**
     * Constructs a new <code>ParseError</code>, with the given information.
     * 
     * @param lineNumber
     *            the line number where the error occurred.
     * @param context
     *            the context in which the error occurred.
     */
    public ParseError(int lineNumber, String context) {
        this.lineNumber = lineNumber;
        this.context = context;
    }

    /**
     * Constructs a new <code>ParseError</code>, with the given information.
     * 
     * @param lineNumber
     *            the line number where the error occurred.
     */
    public ParseError(int lineNumber) {
        this.lineNumber = lineNumber;
        this.context = "";
    }

    /**
     * Constructs a new <code>ParseError</code>, with the given information.
     * 
     * @param context
     *            the context in which the error occurred.
     */
    public ParseError(String context) {
        this.lineNumber = -1;
        this.context = context;
    }
}
