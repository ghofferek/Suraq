/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.main;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;

/**
 * This searches for DomainEquivalences containing ITEs and transforms them.
 * These Equivalences are bad for the GraphReduction. e.g. value0 ==
 * ITE(constraint, value1, value2) --> newbool = ITE(constraint, value0 = value1
 * , value 0 = value2) at the beginning of the formula --> newbool instead of
 * equivalence in Formula
 * 
 * @author Hillebold Christoph
 * 
 */
public class ITEEquationReduction {

    private static boolean _isActive = false;

    public static void setActive(boolean isActive) {
        _isActive = isActive;
    }

    public static boolean isActive() {
        return _isActive;
    }

    /**
     * This searches for DomainEquivalences containing ITEs and transforms them.
     * These Equivalences are bad for the GraphReduction.
     * 
     * @param topLevelFormula
     * @param noDependenceVars
     * @return
     */
    public Formula perform(Formula topLevelFormula, Set<Token> noDependenceVars) {
        if (!_isActive)
            return topLevelFormula;
        List<Formula> andPreList = new ArrayList<Formula>();
        Formula main = topLevelFormula.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList);
        if (andPreList.size() == 0)
            return main;
        else if (andPreList.size() == 1)
            return ImpliesFormula.create(andPreList.get(0), main);
        return ImpliesFormula.create(AndFormula.generate(andPreList), main);
    }

}
