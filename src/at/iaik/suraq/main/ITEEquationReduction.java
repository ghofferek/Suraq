package at.iaik.suraq.main;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;

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
        List<Formula> andPreList = new ArrayList<Formula>();
        Formula main = topLevelFormula.removeDomainITE(topLevelFormula, noDependenceVars, andPreList);
        if(andPreList.size()==0)
            return main;
        else if(andPreList.size()==1)
            return new ImpliesFormula(andPreList.get(0),main);
        return new ImpliesFormula(AndFormula.generate(andPreList),main);
    }
    
}
