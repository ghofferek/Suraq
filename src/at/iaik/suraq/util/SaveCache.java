/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;

/**
 * A class for saving,loading intermediate results to,from file.
 * 
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
public class SaveCache implements Serializable {

    /**
     * unique object version serial number.
     */
    private static final long serialVersionUID = -8044804782114170834L;

    private final Set<PropositionalVariable> propsitionalVars;
    private final Set<DomainVariable> domainVars;
    private final Set<ArrayVariable> arrayVars;
    private final Set<UninterpretedFunction> uninterpretedFunctions;
    private final List<PropositionalVariable> controlVars;

    /**
     * 
     * Constructs a new <code>SaveCache</code>.
     * 
     * @param propsitionalVars
     *            the propsitional variables to store
     * @param domainVars
     *            the domain variables to store
     * @param arrayVars
     *            the array variables to store
     * @param uninterpretedFunctions
     *            the uninterpreted functions to store
     * @param controlVars
     *            the control variables to store
     * @param filename
     *            file to save variables to
     */
    public SaveCache(Set<PropositionalVariable> propsitionalVars,
            Set<DomainVariable> domainVars, Set<ArrayVariable> arrayVars,
            Set<UninterpretedFunction> uninterpretedFunctions,
            List<PropositionalVariable> controlVars, String filename) {
        this.propsitionalVars = propsitionalVars;
        this.domainVars = domainVars;
        this.arrayVars = arrayVars;
        this.uninterpretedFunctions = uninterpretedFunctions;
        this.controlVars = controlVars;

        if (filename != null)
            this.saveToFile(filename);
    }

    /**
     * 
     * Loads a <code>SaveCache</code> from file.
     * 
     * @param filename
     *            file to load variables from.
     * @return the loaded <code>SaveCache</code>
     */
    public static SaveCache loadSaveCacheFromFile(String filename) {
        return readFromFile(filename);
    }

    /**
     * 
     * Write variables to file.
     * 
     * @param filename
     *            file to load variables from.
     */
    private void saveToFile(String filename) {
        try {
            FileOutputStream fout = new FileOutputStream(filename);
            ObjectOutputStream oos = new ObjectOutputStream(fout);
            oos.writeObject(this);
            oos.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    /**
     * 
     * Load variables from file.
     * 
     * @param filename
     *            file to load variables from.
     * @return the loaded <code>SaveCache</code>
     */
    private static SaveCache readFromFile(String filename) {
        SaveCache tmpSaveCache = null;
        try {
            FileInputStream fin = new FileInputStream(filename);
            ObjectInputStream ois = new ObjectInputStream(fin);
            tmpSaveCache = (SaveCache) ois.readObject();
            ois.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
        return tmpSaveCache;
    }

    public Set<PropositionalVariable> getPropsitionalVars() {
        return propsitionalVars;
    }

    public Set<DomainVariable> getDomainVars() {
        return domainVars;
    }

    public Set<ArrayVariable> getArrayVars() {
        return arrayVars;
    }

    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        return uninterpretedFunctions;
    }

    public List<PropositionalVariable> getControlVars() {
        return controlVars;
    }
}
