/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.InvalidParametersException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TermFunctionMacro extends FunctionMacro {

    /**
     * The body of this macro.
     */
    private Term body;

    /**
     * Constructs a new <code>TermFunctionMacro</code> with the given values.
     * 
     * @param name
     *            the name of this macro.
     * @param a
     *            list of parameters
     * @param paramMap
     *            the map from parameters to types.
     * @param body
     *            the actual body.
     * @throws InvalidParametersException
     *             if the size of the parameter list and the type map do not
     *             match.
     */
    public TermFunctionMacro(Token name, List<Token> parameters,
            Map<Token, SExpression> paramMap, Term body)
            throws InvalidParametersException {
        super(name, parameters, paramMap);
        this.body = body;
    }

    /**
     * Constructs a new <code>PropositionalFunctionMacro</code>, which is a deep
     * copy of the given one
     * 
     * @param macro
     *            the macro to (deep) copy.
     */
    public TermFunctionMacro(TermFunctionMacro macro) {
        super(macro);
        this.body = macro.body.deepTermCopy();
    }

    /**
     * Returns the function body of this macro.
     * 
     * @return the <code>body</code>
     */
    public Term getBody() {
        return body;
    }

    /**
     * @see at.iaik.suraq.formula.FunctionMacro#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        // TODO Auto-generated method stub

    }

    /**
     * @see at.iaik.suraq.formula.FunctionMacro#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        // TODO Auto-generated method stub

    }

    /**
     * Returns the type of the term of this macro's body.
     * 
     * @return the type of the term of this macro's body.
     */
    @Override
    public SExpression getType() {
        return body.getType();
    }

    /**
     * @see at.iaik.suraq.formula.EqualityFormula#removeArrayWrites(at.iaik.suraq.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    public Set<Formula> removeArrayWrites(Formula topLevelFormula,
            Set<Token> noDependenceVars) {
        Set<Formula> constraints = new HashSet<Formula>();
        body.removeArrayWrites(topLevelFormula, constraints, noDependenceVars);
        return constraints;
    }

    /**
     * Replaces array-read expressions with uninterpreted function instances
     */
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        body.arrayReadsToUninterpretedFunctions(noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.formula.Term#getUninterpretedFunctions()
     */
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        return body.getUninterpretedFunctions();
    }

    /**
     * @see at.iaik.suraq.formula.FunctionMacro#getBodyExpression()
     */
    @Override
    public SExpression getBodyExpression() {
        return body.toSmtlibV2();
    }

    /**
     * @see at.iaik.suraq.formula.Term#substituteUninterpretedFunction(at.iaik.suraq.formula.UninterpretedFunction,
     *      at.iaik.suraq.formula.UninterpretedFunction)
     */
    public void substituteUninterpretedFunction(
            UninterpretedFunction oldFunction, UninterpretedFunction newFunction) {
        body.substituteUninterpretedFunction(oldFunction, newFunction);
    }
}
