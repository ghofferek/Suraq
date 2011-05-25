/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.exceptions;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class InvalidValueConstraintException extends SuraqException {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * Constructs a new <code>InvalidValueConstraintException</code>.
     */
    public InvalidValueConstraintException() {
        super();
    }

    /**
     * Constructs a new <code>InvalidValueConstraintException</code>.
     * 
     * @param message
     * @param cause
     */
    public InvalidValueConstraintException(String message, Throwable cause) {
        super(message, cause);
    }

    /**
     * Constructs a new <code>InvalidValueConstraintException</code>.
     * 
     * @param message
     */
    public InvalidValueConstraintException(String message) {
        super(message);
    }

    /**
     * Constructs a new <code>InvalidValueConstraintException</code>.
     * 
     * @param cause
     */
    public InvalidValueConstraintException(Throwable cause) {
        super(cause);
    }

}
