/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.exceptions;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class WrongNumberOfParametersException extends SuraqException {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * Constructs a new <code>WrongNumberOfParametersException</code>.
     */
    public WrongNumberOfParametersException() {
        super();
    }

    /**
     * Constructs a new <code>WrongNumberOfParametersException</code>.
     * 
     * @param message
     * @param cause
     */
    public WrongNumberOfParametersException(String message, Throwable cause) {
        super(message, cause);
    }

    /**
     * Constructs a new <code>WrongNumberOfParametersException</code>.
     * 
     * @param message
     */
    public WrongNumberOfParametersException(String message) {
        super(message);
    }

    /**
     * Constructs a new <code>WrongNumberOfParametersException</code>.
     * 
     * @param cause
     */
    public WrongNumberOfParametersException(Throwable cause) {
        super(cause);
    }
}
