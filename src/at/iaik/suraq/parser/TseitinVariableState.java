/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.parser;

/**
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 *         Variables in this data structure are used to check if a clause
 *         belongs to the definition of a tseitin variable.
 */
public class TseitinVariableState {
    /**
     * defines if the tseitin variable occurred at the beginning of the clause.
     */
    private boolean frontOccurrence;
    /**
     * indicates if a sign change has happened already.
     */
    private boolean signChange;
    /**
     * indicates the sign of the tseitin variable.
     */
    private boolean sign;

    public TseitinVariableState(boolean frontOccurrence, boolean signChange,
            boolean sign) {
        this.frontOccurrence = frontOccurrence;
        this.signChange = signChange;
        this.sign = sign;
    }

    /**
     * @return the frontOccurrence
     */
    public boolean isFrontOccurrence() {
        return frontOccurrence;
    }

    /**
     * @param frontOccurrence
     *            the frontOccurrence to set
     */
    public void setFrontOccurrence(boolean frontOccurrence) {
        this.frontOccurrence = frontOccurrence;
    }

    /**
     * @return the signedChange
     */
    public boolean isSignedChange() {
        return signChange;
    }

    /**
     * @param signedChange
     *            the signedChange to set
     */
    public void setSignedChange(boolean signedChange) {
        this.signChange = signedChange;
    }

    /**
     * @param sign
     *            the sign to set
     */
    public boolean isSign() {
        return sign;
    }

    /**
     * @param sign
     *            the sign to set
     */
    public void setSign(boolean sign) {
        this.sign = sign;
    }

}
