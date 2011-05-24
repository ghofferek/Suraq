/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.exceptions;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class InvalidIndexGuardException extends SuraqException {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * Constructs a new <code>InvalidIndexGuardException</code>.
     */
    public InvalidIndexGuardException() {
        super();
    }

    /**
     * Constructs a new <code>InvalidIndexGuardException</code>.
     * 
     * @param message
     * @param cause
     */
    public InvalidIndexGuardException(String message, Throwable cause) {
        super(message, cause);
    }

    /**
     * Constructs a new <code>InvalidIndexGuardException</code>.
     * 
     * @param message
     */
    public InvalidIndexGuardException(String message) {
        super(message);
    }

    /**
     * Constructs a new <code>InvalidIndexGuardException</code>.
     * 
     * @param cause
     */
    public InvalidIndexGuardException(Throwable cause) {
        super(cause);
    }

}
