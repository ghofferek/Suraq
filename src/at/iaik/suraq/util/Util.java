/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.List;
import java.util.Set;

import at.iaik.suraq.formula.ArrayVariable;
import at.iaik.suraq.formula.DomainVariable;
import at.iaik.suraq.formula.Formula;
import at.iaik.suraq.formula.PropositionalVariable;
import at.iaik.suraq.formula.Term;
import at.iaik.suraq.sexp.Token;

/**
 * 
 * Collection of (static) utility methods.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class Util {

    /**
     * Chooses a fresh variable name with respect to the given formula. The name
     * is also distinct from present macro names and uninterpreted function
     * names.
     * 
     * @param formula
     *            the formula
     * @param prefix
     *            a prefix that should be included in the variable name
     * @return a fresh variable name (w.r.t.<code>formula</code>), starting with
     *         <code>prefix</code>.
     */
    public static final String freshVarName(Formula formula, String prefix) {
        Set<ArrayVariable> arrayVars = formula.getArrayVariables();
        Set<DomainVariable> domainVars = formula.getDomainVariables();
        Set<PropositionalVariable> propVars = formula
                .getPropositionalVariables();
        Set<String> functionNames = formula.getUninterpretedFunctionNames();
        Set<String> macroNames = formula.getFunctionMacroNames();

        int count = -1;
        while (count++ >= 0) {
            String name = prefix + (count == 0 ? ("_fresh" + count) : "");
            if (arrayVars.contains(new ArrayVariable(name)))
                continue;
            if (domainVars.contains(new DomainVariable(name)))
                continue;
            if (propVars.contains(new PropositionalVariable(name)))
                continue;
            if (functionNames.contains(name))
                continue;
            if (macroNames.contains(name))
                continue;
            return name;
        }
        throw new RuntimeException("Could not create fresh variable name.");
    }

    /**
     * Checks whether the given formula contains any of the given tokens as
     * identifiers.
     * 
     * @param formula
     *            the formula to check
     * @param names
     *            the <code>Token</code>s to check the formula against.
     * @return <code>true</code> if at least one of the <code>Token</code>s from
     *         <code>names</code>, occurred in <code>formula</code>,
     *         <code>false</code> otherwise.
     */
    public static final boolean formulaContainsAny(Formula formula,
            Set<Token> names) {
        Set<ArrayVariable> arrayVars = formula.getArrayVariables();
        Set<DomainVariable> domainVars = formula.getDomainVariables();
        Set<PropositionalVariable> propVars = formula
                .getPropositionalVariables();
        Set<String> functionNames = formula.getUninterpretedFunctionNames();
        Set<String> macroNames = formula.getFunctionMacroNames();

        for (Token token : names) {
            if (arrayVars.contains(new ArrayVariable(token)))
                return true;
            if (domainVars.contains(new DomainVariable(token)))
                return true;
            if (propVars.contains(new PropositionalVariable(token)))
                return true;
            if (functionNames.contains(token))
                return true;
            if (macroNames.contains(token))
                return true;
        }
        return false;
    }

    /**
     * Checks whether the given term contains any of the given tokens as
     * identifiers.
     * 
     * @param term
     *            the term to check
     * @param names
     *            the <code>Token</code>s to check the formula against.
     * @return <code>true</code> if at least one of the <code>Token</code>s from
     *         <code>names</code>, occurred in <code>term</code>,
     *         <code>false</code> otherwise.
     */
    public static final boolean termContainsAny(Term term, Set<Token> names) {
        Set<ArrayVariable> arrayVars = term.getArrayVariables();
        Set<DomainVariable> domainVars = term.getDomainVariables();
        Set<PropositionalVariable> propVars = term.getPropositionalVariables();
        Set<String> functionNames = term.getUninterpretedFunctionNames();
        Set<String> macroNames = term.getFunctionMacroNames();

        for (Token token : names) {
            if (arrayVars.contains(new ArrayVariable(token)))
                return true;
            if (domainVars.contains(new DomainVariable(token)))
                return true;
            if (propVars.contains(new PropositionalVariable(token)))
                return true;
            if (functionNames.contains(token))
                return true;
            if (macroNames.contains(token))
                return true;
        }
        return false;
    }

    /**
     * Chooses a fresh variable name w.r.t. the given formula.
     * 
     * @param formula
     *            the formula.
     * @return a fresh variable name w.r.t. <code>formula</code>
     */
    public static final String freshVarName(Formula formula) {
        return Util.freshVarName(formula, "");
    }

    /**
     * Increments the given list of (modular) counters.
     * 
     * @param counters
     * @return <code>true</code> if the counters did not (overall) overflow,
     *         <code>false</code> otherwise.
     */
    public static boolean incrementCounters(List<Integer> counters) {
        int k = counters.size();
        int count = 0;
        do {
            if (counters.get(count) == k - 1) {
                counters.set(count, 0);
                count++;
            } else {
                counters.set(count, counters.get(count) + 1);
                return true;
            }
        } while (count < k);
        return false;
    }

}
