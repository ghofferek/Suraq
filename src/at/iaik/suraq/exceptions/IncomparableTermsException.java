/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.exceptions;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class IncomparableTermsException extends SuraqException {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * Constructs a new <code>IncomparableTermsException</code>.
     */
    public IncomparableTermsException() {
        super();
    }

    /**
     * Constructs a new <code>IncomparableTermsException</code>.
     * 
     * @param message
     * @param cause
     */
    public IncomparableTermsException(String message, Throwable cause) {
        super(message, cause);
    }

    /**
     * Constructs a new <code>IncomparableTermsException</code>.
     * 
     * @param message
     */
    public IncomparableTermsException(String message) {
        super(message);
    }

    /**
     * Constructs a new <code>IncomparableTermsException</code>.
     * 
     * @param cause
     */
    public IncomparableTermsException(Throwable cause) {
        super(cause);
    }
}
