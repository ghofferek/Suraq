package at.iaik.suraq.main;

import java.util.Set;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;

public class ITEEquationReduction {

    private static boolean _isActive = true;
    public static void setActive(boolean isActive)
    {
        _isActive = isActive;
    }
    public static boolean isActive()
    {
        return _isActive;
    }
    
    public Formula performReduction(Formula topLevelFormula, Set<Token> noDependenceVars)
    {
        if(!_isActive)
            return topLevelFormula;
        return topLevelFormula.removeDomainITE(topLevelFormula, noDependenceVars);
    }
    
}
