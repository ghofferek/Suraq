/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.text.DecimalFormat;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
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
    private final Z3Proof proof;
    private final Integer instanceCounter;
    private final Formula mainFormula;
    private final Map<Integer, Formula> assertPartitionFormulas;
    private final Map<PropositionalVariable, Formula> tseitinEncoding;
    private final Map<Set<?>, ImmutableSet<?>> immutableSetInstances;
    private final Map<Object, Object> immutableSetUniqueElements;

    public SaveCache(Set<PropositionalVariable> propsitionalVars,
            Set<DomainVariable> domainVars, Set<ArrayVariable> arrayVars,
            Set<UninterpretedFunction> uninterpretedFunctions,
            List<PropositionalVariable> controlVars, Formula mainFormula,
            Map<Integer, Formula> assertPartitionFormulas,
            Map<PropositionalVariable, Formula> tseitinEncoding, Z3Proof proof,
            Map<Set<?>, ImmutableSet<?>> immutableSetInstances,
            Map<Object, Object> immutableSetUniqueElements, String filename) {

        this.propsitionalVars = propsitionalVars;
        this.domainVars = domainVars;
        this.arrayVars = arrayVars;
        this.uninterpretedFunctions = uninterpretedFunctions;
        this.controlVars = controlVars;
        this.proof = proof;
        this.instanceCounter = Z3Proof.getInstanceCounter();
        this.mainFormula = mainFormula;
        this.assertPartitionFormulas = assertPartitionFormulas;
        this.tseitinEncoding = tseitinEncoding;
        this.immutableSetInstances = immutableSetInstances;
        this.immutableSetUniqueElements = immutableSetUniqueElements;

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
        SaveCache intermediateVars = SaveCache.readFromFile(filename);

        // if serial cache, restore STATIC Z3Proof Instance counter
        if (intermediateVars.getInstanceCounter() != null) {
            DecimalFormat myFormatter = new DecimalFormat("###,###,###");
            String counter = myFormatter.format(intermediateVars
                    .getInstanceCounter());
            System.out
                    .println("INFO: RESTORING STATIC Z3PROOF INSTANCE COUNTER! ("
                            + counter + ")");
            Z3Proof.setInstanceCounter(intermediateVars.getInstanceCounter());
            System.out
                    .println("INFO: RESTORING STATIC ELEMENTS OF IMMUTABLE SETS!");
            ImmutableSet.setInstances(intermediateVars
                    .getImmutableSetInstances());
            ImmutableSet.setUniqueElements(intermediateVars
                    .getImmutableSetUniqueElements());

        }
        System.out.println();

        return intermediateVars;
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

    public Z3Proof getProof() {
        return this.proof;
    }

    public Integer getInstanceCounter() {
        return this.instanceCounter;
    }

    public Formula getMainFormula() {
        return this.mainFormula;
    }

    public Map<Integer, Formula> getAssertPartitionFormulas() {
        return this.assertPartitionFormulas;
    }

    public Map<PropositionalVariable, Formula> getTseitinEncoding() {
        return this.tseitinEncoding;
    }

    /**
     * @return the <code>immutableSetInstances</code>
     */
    public Map<Set<?>, ImmutableSet<?>> getImmutableSetInstances() {
        return immutableSetInstances;
    }

    /**
     * @return the <code>immutableSetUniqueElements</code>
     */
    public Map<Object, Object> getImmutableSetUniqueElements() {
        return immutableSetUniqueElements;
    }
}