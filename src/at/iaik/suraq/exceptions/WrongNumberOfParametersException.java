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
        // TODO Auto-generated constructor stub
    }

    /**
     * Constructs a new <code>WrongNumberOfParametersException</code>.
     * 
     * @param message
     * @param cause
     */
    public WrongNumberOfParametersException(String message, Throwable cause) {
        super(message, cause);
        // TODO Auto-generated constructor stub
    }

    /**
     * Constructs a new <code>WrongNumberOfParametersException</code>.
     * 
     * @param message
     */
    public WrongNumberOfParametersException(String message) {
        super(message);
        // TODO Auto-generated constructor stub
    }

    /**
     * Constructs a new <code>WrongNumberOfParametersException</code>.
     * 
     * @param cause
     */
    public WrongNumberOfParametersException(Throwable cause) {
        super(cause);
        // TODO Auto-generated constructor stub
    }
    // TODO implement!
}
