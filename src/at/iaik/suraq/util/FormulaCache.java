/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.util;

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.WeakHashMap;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndOrXorFormula;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.FormulaTerm;
import at.iaik.suraq.smtlib.formula.FunctionMacro;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;

public class FormulaCache<T> {
    // This static List MUST be on first position in this file!
    // Else it would not be initialized before the other static variables
    private static ArrayList<FormulaCache<?>> instances = new ArrayList<FormulaCache<?>>();

    // do not cache token because token is a sexpression that has recursive
    // problems??
    public static FormulaCache<Token> token = new FormulaCache<Token>("Token",
            true);
    public static FormulaCache<NotFormula> notFormula = new FormulaCache<NotFormula>(
            "NOT", true);
    public static FormulaCache<PropositionalVariable> propVar = new FormulaCache<PropositionalVariable>(
            "PropVar", true);
    public static FormulaCache<PropositionalConstant> propConst = new FormulaCache<PropositionalConstant>(
            "PropConst", true);
    public static FormulaCache<DomainVariable> domainVarFormula = new FormulaCache<DomainVariable>(
            "DomainVar", true);
    public static FormulaCache<ImpliesFormula> impliesFormula = new FormulaCache<ImpliesFormula>(
            "implies", true);
    public static FormulaCache<AndOrXorFormula> andOrXorFormula = new FormulaCache<AndOrXorFormula>(
            "AndOrXor", true);
    public static FormulaCache<FormulaTerm> formulaTerm = new FormulaCache<FormulaTerm>(
            "FormulaTerm", true);
    public static FormulaCache<EqualityFormula> equalityFormula = new FormulaCache<EqualityFormula>(
            "EqualityFormula", true);
    public static FormulaCache<DomainTerm> domainTerm = new FormulaCache<DomainTerm>(
            "DomainTerm:*", true);
    public static FormulaCache<Term> term = new FormulaCache<Term>("Term:*",
            true);
    public static FormulaCache<Formula> formula = new FormulaCache<Formula>(
            "Formula:*", true);
    public static FormulaCache<UninterpretedFunction> uninterpretedFunction = new FormulaCache<UninterpretedFunction>(
            "UF", true);
    public static FormulaCache<FunctionMacro> functionMacro = new FormulaCache<FunctionMacro>(
            "FunctionMacro", true);

    public static boolean _isActive = true;

    private boolean _isActiveLocal = true;

    // For statistics
    private long cachedReads = 0;
    private long cachedWrites = 0;

    // Sets are not possible, because they don't provide the get() method
    // WeakHashMap compares keys with equals(==) instead of .hashCode!!!!
    // http://docs.oracle.com/javase/6/docs/api/java/util/WeakHashMap.html

    private WeakHashMap<T, WeakReference<T>> cache = new WeakHashMap<T, WeakReference<T>>();
    private String name;

    private FormulaCache(String name, boolean isActive2) {
        this._isActiveLocal = isActive2;
        try {
            this.name = name;
            FormulaCache.instances.add(this);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException("blubb");
        }
    }

    /**
     * Clears all caches.
     */
    public static void clearAll() {
        for (FormulaCache<?> instance : FormulaCache.instances) {
            instance.clear();
        }
    }

    /**
     * Clears the cache and resets the statistic.
     */
    public void clear() {
        cache.clear();
        cachedReads = 0;
    }

    /**
     * This may override an existing object with the same hashCode.
     * 
     * @param object
     * @throws ClassCastException
     */
    public void post(T object) throws ClassCastException {
        if (!FormulaCache._isActive || !_isActiveLocal)
            return;
        cache.put(object, new WeakReference<T>(object));
        cachedWrites++;
    }

    /**
     * This method returns an Object with the same hashCode if it already
     * exists. If not, the given Object is stored in the Map. If you modify the
     * given Object later, it will be changed everywhere!!!
     * 
     * @param object
     * @return
     * @throws ClassCastException
     */
    public T put(T object) throws ClassCastException {
        if (!FormulaCache._isActive || !_isActiveLocal)
            return object;

        if (cache.containsKey(object)) {
            T result = cache.get(object).get();
            if (result != null) {
                if (result != object) {
                    cachedReads++;
                    if (cachedReads % 10000000 == 0)
                        this.printStatisticLine();
                }
                return result;
            }
        }
        cache.put(object, new WeakReference<T>(object));
        cachedWrites++;
        if (cachedWrites % 100000 == 0)
            this.printStatisticLine();
        return object;
    }

    /**
     * Gets an already existing instance of the given reference object. If the
     * Object does not exist, this method returns null
     * 
     * @param reference
     * @return
     * @throws ClassCastException
     */
    public T get(T reference) throws ClassCastException {
        if (!FormulaCache._isActive || !_isActiveLocal)
            return reference;
        if (cache.containsKey(reference)) {
            T result = cache.get(reference).get();
            if (result != reference && result != null)
                cachedReads++;
            return result;
        }
        return null;
    }

    public long getCachedReads() {
        return cachedReads;
    }

    public long getCachedWrites() {
        return cachedWrites;
    }

    public int getCachedElements() {
        return cache.size();
    }

    public String getName() {
        return name;
    }

    public void printStatisticLine() {
        long reads = getCachedReads();
        int elems = getCachedElements();
        long writes = getCachedWrites();
        String className = getName();
        System.err.println("* saved " + reads + " reads on " + elems
                + " elements of max. " + writes + ":" + className);
    }

    public static void printStatistic() {
        System.out.println("************************************************");
        for (FormulaCache<?> instance : FormulaCache.instances) {
            long reads = instance.getCachedReads();
            int elems = instance.getCachedElements();
            long writes = instance.getCachedWrites();
            String className = instance.getName();
            System.out.println("* saved " + reads + " reads on " + elems
                    + " elements of max. " + writes + ":" + className);
        }
        System.out.println("************************************************");

    }

}
