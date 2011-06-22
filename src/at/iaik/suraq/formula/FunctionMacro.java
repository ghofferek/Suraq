/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import at.iaik.suraq.exceptions.InvalidParametersException;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * This class represents a (Boolean) function macro. It represents the
 * "define-fun" part of the input. Do not confuse it with
 * <code>FunctionMacroInstance</code> which is an actual instance of a macro.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class FunctionMacro {

    /**
     * The name of this macro.
     */
    private final Token name;

    private final List<Token> parameters;

    /**
     * The map of parameters to their types.
     */
    private final Map<Token, SExpression> paramMap;

    /**
     * The body of this macro.
     */
    private Formula body;

    /**
     * Constructs a new <code>FunctionMacro</code> with the given values.
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
    public FunctionMacro(Token name, List<Token> parameters,
            Map<Token, SExpression> paramMap, Formula body)
            throws InvalidParametersException {
        if (parameters.size() != paramMap.size())
            throw new InvalidParametersException();
        for (Token parameter : parameters) {
            if (!paramMap.containsKey(parameter))
                throw new InvalidParametersException();
            if (paramMap.get(parameter) == null)
                throw new InvalidParametersException();
        }
        this.name = name;
        this.parameters = new ArrayList<Token>(parameters);
        this.paramMap = new HashMap<Token, SExpression>(paramMap);
        this.body = body;
    }

    /**
     * Constructs a new <code>FunctionMacro</code>, which is a deep copy of the
     * given one
     * 
     * @param macro
     *            the macro to (deep) copy.
     */
    public FunctionMacro(FunctionMacro macro) {

        this.name = (Token) macro.name.deepCopy();
        this.parameters = new ArrayList<Token>();
        for (Token parameter : macro.parameters)
            this.parameters.add((Token) parameter.deepCopy());
        this.paramMap = new HashMap<Token, SExpression>();
        for (Token token : macro.paramMap.keySet())
            this.paramMap.put((Token) token.deepCopy(),
                    macro.paramMap.get(token).deepCopy());
        this.body = macro.body.deepFormulaCopy();
    }

    /**
     * @return the <code>name</code>
     */
    public Token getName() {
        return name;
    }

    /**
     * Returns a copy of the list of parameters.
     * 
     * @return the <code>parameters</code> (copy)
     */
    public List<Token> getParameters() {
        return new ArrayList<Token>(parameters);
    }

    /**
     * Returns a copy of the map from parameters to values.
     * 
     * @return the <code>paramMap</code>
     */
    public Map<Token, SExpression> getParamMap() {
        return new HashMap<Token, SExpression>(paramMap);
    }

    /**
     * Returns the number of parameters of this macro.
     * 
     * @return the number of parameters.
     */
    public int getNumParams() {
        assert (parameters.size() == paramMap.size());
        return parameters.size();
    }

    /**
     * Returns the type of the parameter with index <code>count</code>, or
     * <code>null</code> if the index is out of bounds.
     * 
     * @param index
     *            the index of the parameter to look up.
     * @return the type of the parameter with the given index, or
     *         <code>null</code> if no such parameter exists.
     */
    public SExpression getParamType(int index) {
        try {
            return paramMap.get(parameters.get(index));
        } catch (IndexOutOfBoundsException exc) {
            return null;
        }
    }

    /**
     * Returns the type of the parameter with the given name, or
     * <code>null</code> if no such parameter exists..
     * 
     * @param param
     *            the name of the parameter to look up.
     * @return the type of the parameter with the given name, or
     *         <code>null</code> if no such parameter exists.
     */
    public SExpression getParamType(Token param) {
        return paramMap.get(param);
    }

    /**
     * Returns the parameter name with the given index.
     * 
     * @param index
     *            the index to look up
     * @return the parameter name with the given index.
     */
    public Token getParam(int index) {
        return parameters.get(index);
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
    public FunctionMacro negationNormalForm() throws SuraqException {
        assert (!name.toString().endsWith("NNF"));

        Token nnfName = new Token(name.toString() + "NNF");
        Map<Token, SExpression> nnfParamMap = new HashMap<Token, SExpression>(
                paramMap);
        List<Token> nnfParameters = new ArrayList<Token>(parameters);

        Formula nnfBody = body.negationNormalForm();

        return new FunctionMacro(nnfName, nnfParameters, nnfParamMap, nnfBody);
    }

    /**
     * Creates a macro with negated body, put in NNF.
     * 
     * @return a macro with a negated body, put in NNF.
     * @throws SuraqException
     */
    public FunctionMacro negatedMacro() throws SuraqException {
        Token negatedName = new Token(name.toString() + "Negated");
        Map<Token, SExpression> negatedParamMap = new HashMap<Token, SExpression>(
                paramMap);
        List<Token> negatedParameters = new ArrayList<Token>(parameters);

        Formula negatedBody = (new NotFormula(body)).negationNormalForm();

        return new FunctionMacro(negatedName, negatedParameters,
                negatedParamMap, negatedBody);
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof FunctionMacro))
            return false;
        FunctionMacro other = (FunctionMacro) obj;
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
     * 
     */
    public void removeArrayEqualities() {
        if (body instanceof ArrayEq)
            body = ((ArrayEq) body).toArrayProperties();
        else
            body.removeArrayEqualities();
    }

}
