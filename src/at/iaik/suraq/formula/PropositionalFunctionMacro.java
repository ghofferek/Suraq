/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.InvalidParametersException;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * This class represents a (Boolean) function macro. It represents the
 * "define-fun" part of the input. Do not confuse it with
 * <code>PropositionalFunctionMacroInstance</code> which is an actual instance
 * of a macro.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalFunctionMacro extends FunctionMacro {

    /**
     * The body of this macro.
     */
    private Formula body;

    /**
     * Constructs a new <code>PropositionalFunctionMacro</code> with the given
     * values.
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
    public PropositionalFunctionMacro(Token name, List<Token> parameters,
            Map<Token, SExpression> paramMap, Formula body)
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
    public PropositionalFunctionMacro(PropositionalFunctionMacro macro) {
        super(macro);
        this.body = macro.body.deepFormulaCopy();
    }

    /**
     * Returns the function body of this macro.
     * 
     * @return the <code>body</code>
     */
    public Formula getBody() {
        return body;
    }

    /**
     * Creates a new macro, which is the same as this one, but in NNF.
     * 
     * @return a copy of this macro in NNF.
     * @throws SuraqException
     *             if conversion to NNF fails (e.g. due to invalid array
     *             properties)
     */
    public PropositionalFunctionMacro negationNormalForm()
            throws SuraqException {
        assert (!name.toString().endsWith("NNF"));

        Token nnfName = new Token(name.toString() + "NNF");
        Map<Token, SExpression> nnfParamMap = new HashMap<Token, SExpression>(
                paramMap);
        List<Token> nnfParameters = new ArrayList<Token>(parameters);

        Formula nnfBody = body.negationNormalForm();

        return new PropositionalFunctionMacro(nnfName, nnfParameters,
                nnfParamMap, nnfBody);
    }

    /**
     * Creates a macro with negated body, put in NNF.
     * 
     * @return a macro with a negated body, put in NNF.
     * @throws SuraqException
     */
    public PropositionalFunctionMacro negatedMacro() throws SuraqException {
        Token negatedName = new Token(name.toString() + "Negated");
        Map<Token, SExpression> negatedParamMap = new HashMap<Token, SExpression>(
                paramMap);
        List<Token> negatedParameters = new ArrayList<Token>(parameters);

        Formula negatedBody = (new NotFormula(body)).negationNormalForm();

        return new PropositionalFunctionMacro(negatedName, negatedParameters,
                negatedParamMap, negatedBody);
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof PropositionalFunctionMacro))
            return false;
        PropositionalFunctionMacro other = (PropositionalFunctionMacro) obj;
        return other.name.equals(name) && other.parameters.equals(parameters)
                && other.paramMap.equals(paramMap) && other.body.equals(body);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return name.hashCode() ^ parameters.hashCode() ^ paramMap.hashCode()
                ^ body.hashCode();
    }

    /**
     * Removes array equalities from the body of the macro.
     */
    @Override
    public void removeArrayEqualities() {
        if (body instanceof ArrayEq)
            body = ((ArrayEq) body).toArrayProperties();
        else
            body.removeArrayEqualities();
    }

    /**
     * Converts array properties in the body of the macro to finite conjunctions
     * 
     * @param indexSet
     *            the index set.
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        if (body instanceof ArrayProperty)
            body = ((ArrayProperty) body).toFiniteConjunction(indexSet);
        else
            body.arrayPropertiesToFiniteConjunctions(indexSet);
    }

    /**
     * Simplifies the body of the macro.
     */
    public void simplify() {
        body = body.simplify();
    }

    /**
     * Simplifies the body of the macro after substituting local variables
     * according to the given map. If the result is a constant, it is returned
     * as a <code>Boolean</code>. Otherwise, <code>null</code> is returned.
     * 
     * @param paramMap
     *            the map for substituting local variables.
     * @return <code>null</code>, if simplifcation does not yield a constant.
     *         The constant as a <code>Boolean</code> otherwise.
     */
    public Boolean simplify(Map<Token, Term> paramMap) {

        Formula bodyCopy = body.deepFormulaCopy();

        bodyCopy.substituteFormula(paramMap);
        bodyCopy = bodyCopy.simplify();

        if (bodyCopy instanceof PropositionalConstant)
            return ((PropositionalConstant) bodyCopy).getValue();

        return null;
    }

    /**
     * @see at.iaik.suraq.formula.FunctionMacro#getType()
     */
    @Override
    public SExpression getType() {
        return SExpressionConstants.BOOL_TYPE;
    }

    /**
     * @param topLevelFormula
     */
    public Set<Formula> removeArrayWrites(Formula topLevelFormula) {
        Set<Formula> constraints = new HashSet<Formula>();
        body.removeArrayWrites(topLevelFormula, constraints);
        return constraints;
    }
}
