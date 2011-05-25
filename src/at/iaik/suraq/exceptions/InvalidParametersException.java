/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.exceptions;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class InvalidParametersException extends SuraqException {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * Constructs a new <code>InvalidParametersException</code>.
     */
    public InvalidParametersException() {
        super();
    }

    /**
     * Constructs a new <code>InvalidParametersException</code>.
     * 
     * @param message
     * @param cause
     */
    public InvalidParametersException(String message, Throwable cause) {
        super(message, cause);
    }

    /**
     * Constructs a new <code>InvalidParametersException</code>.
     * 
     * @param message
     */
    public InvalidParametersException(String message) {
        super(message);
    }

    /**
     * Constructs a new <code>InvalidParametersException</code>.
     * 
     * @param cause
     */
    public InvalidParametersException(Throwable cause) {
        super(cause);
    }
}
