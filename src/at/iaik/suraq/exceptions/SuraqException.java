/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.exceptions;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class SuraqException extends Exception {

    /**
     * Default value.
     */
    private static final long serialVersionUID = 1L;

    /**
	 * 
	 */
    public SuraqException() {
        super();
    }

    /**
     * Constructs a new exception with the specified detail message and cause.
     * 
     * @param message
     *            the detail message.
     * @param cause
     *            the cause
     */
    public SuraqException(String message, Throwable cause) {
        super(message, cause);
    }

    /**
     * Constructs a new exception with the specified detail message.
     * 
     * @param message
     *            the detail message.
     */
    public SuraqException(String message) {
        super(message);

    }

    /**
     * Constructs a new exception with the specified cause.
     * 
     * @param cause
     *            the cause
     */
    public SuraqException(Throwable cause) {
        super(cause);
    }

}
