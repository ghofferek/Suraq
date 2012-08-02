/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.exceptions;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class WrongFunctionTypeException extends SuraqException {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * Constructs a new <code>WrongNumberOfParametersException</code>.
     */
    public WrongFunctionTypeException() {
    }

    /**
     * Constructs a new <code>WrongNumberOfParametersException</code>.
     * 
     * @param message
     * @param cause
     */
    public WrongFunctionTypeException(String message, Throwable cause) {
        super(message, cause);
    }

    /**
     * Constructs a new <code>WrongNumberOfParametersException</code>.
     * 
     * @param message
     */
    public WrongFunctionTypeException(String message) {
        super(message);
    }

    /**
     * Constructs a new <code>WrongNumberOfParametersException</code>.
     * 
     * @param cause
     */
    public WrongFunctionTypeException(Throwable cause) {
        super(cause);
    }
}
