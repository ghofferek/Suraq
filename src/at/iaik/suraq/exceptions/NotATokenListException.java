/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.exceptions;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class NotATokenListException extends SuraqException {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * Constructs a new <code>NotATokenListException</code>.
     */
    public NotATokenListException() {
        super();
    }

    /**
     * Constructs a new <code>NotATokenListException</code>.
     * 
     * @param message
     * @param cause
     */
    public NotATokenListException(String message, Throwable cause) {
        super(message, cause);

    }

    /**
     * Constructs a new <code>NotATokenListException</code>.
     * 
     * @param message
     */
    public NotATokenListException(String message) {
        super(message);

    }

    /**
     * Constructs a new <code>NotATokenListException</code>.
     * 
     * @param cause
     */
    public NotATokenListException(Throwable cause) {
        super(cause);

    }
}
