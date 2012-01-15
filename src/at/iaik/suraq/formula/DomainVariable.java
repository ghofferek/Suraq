/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * A class representing domain variables.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class DomainVariable extends DomainTerm {
    /**
     * The name of the variable.
     */
    private final String varName;

    /**
     * 
     * Constructs a new <code>DomainVariable</code>.
     * 
     * @param varName
     *            the name of the variable.
     */
    public DomainVariable(String varName) {
        this.varName = varName;
    }

    /**
     * 
     * Constructs a new <code>DomainVariable</code>.
     * 
     * @param name
     *            the <code>Token</code> representing the variable name.
     */
    public DomainVariable(Token name) {
        this.varName = name.toString();
    }

    /**
     * Get the variable name.
     * 
     * @return the <code>varName</code>
     */
    public String getVarName() {
        return varName;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof DomainVariable))
            return false;
        return varName.equals(((DomainVariable) obj).varName);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return varName.hashCode();
    }

    /**
     * @see at.iaik.suraq.formula.DomainTerm#isEvar(java.util.Collection)
     */
    @Override
    public boolean isEvar(Collection<DomainVariable> uVars) {
        return !uVars.contains(this);
    }

    /**
     * @see at.iaik.suraq.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return new DomainVariable(new String(varName));
    }

    /**
     * @see at.iaik.suraq.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        return new HashSet<ArrayVariable>();
    }

    /**
     * @see at.iaik.suraq.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> result = new HashSet<DomainVariable>();
        result.add(new DomainVariable(varName));
        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        return new HashSet<PropositionalVariable>();
    }

    /**
     * @see at.iaik.suraq.formula.Term#getFunctionMacroNames()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        return new HashSet<FunctionMacro>();
    }

    /**
     * @see at.iaik.suraq.formula.Term#getFunctionMacros()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        return new HashSet<String>();
    }

    /**
     * @see at.iaik.suraq.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        return new HashSet<String>();
    }

    /**
     * @see at.iaik.suraq.formula.Term#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        return new HashSet<DomainTerm>();
    }

    /**
     * @see at.iaik.suraq.formula.Term#substituteTerm(java.util.Map)
     */
    @Override
    public Term substituteTerm(Map<Token, Term> paramMap) {
        if (paramMap.containsKey(new Token(varName)))
            return paramMap.get(new Token(varName));
        else
            return this;
    }

    /**
     * @see at.iaik.suraq.formula.Term#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        return new Token(varName);
    }

    /**
     * @see at.iaik.suraq.formula.Term#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        // nothing to do here
        return;
    }

    /**
     * @see at.iaik.suraq.formula.Term#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        // nothing to do here
        return;
    }

    /**
     * @see at.iaik.suraq.formula.Term#removeArrayWrites(at.iaik.suraq.formula.Formula)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        // nothing to do
        return;
    }

    /**
     * @see at.iaik.suraq.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        // nothing to do
        return;
    }

    /**
     * @see at.iaik.suraq.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        return new HashSet<UninterpretedFunction>();
    }

    /**
     * @see at.iaik.suraq.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.formula.UninterpretedFunction)
     */
    @Override
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        return;
    }

    /**
     * @see at.iaik.suraq.formula.Term#flatten()
     */
    @Override
    public Term flatten() {
        return new DomainVariable(varName);
    }

    /**
     * @see at.iaik.suraq.formula.Term#makeArrayReadsSimple(java.util.Set,
     *      at.iaik.suraq.formula.Formula, java.util.Set)
     */
    @Override
    public void makeArrayReadsSimple(Set<Formula> constraints,
            Formula topLevelFormula, Set<Token> noDependenceVars) {
        return;
    }

}
