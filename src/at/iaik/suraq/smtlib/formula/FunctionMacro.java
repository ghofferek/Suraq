/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.InvalidParametersException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class FunctionMacro {

    /**
     * The name of this macro.
     */
    protected final Token name;
    protected final List<Token> parameters;
	
    /**
     * The map of parameters to their types.
     */
    protected final Map<Token, SExpression> paramMap;

    /**
     * Constructs a new <code>FunctionMacro</code> with the given values.
     * 
     * @param name
     *            the name of this macro.
     * @param a
     *            list of parameters
     * @param paramMap
     *            the map from parameters to types.
     * @throws InvalidParametersException
     *             if the size of the parameter list and the type map do not
     *             match.
     */
    protected FunctionMacro(Token name, List<Token> parameters,
            Map<Token, SExpression> paramMap) throws InvalidParametersException {
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
     * Removes array equalities from the body of the macro.
     */
    public abstract FunctionMacro removeArrayEqualities();

    /**
     * Converts array properties in the body of the macro to finite conjunctions
     * 
     * @param indexSet
     *            the index set.
     */
    public abstract FunctionMacro arrayPropertiesToFiniteConjunctions(
            Set<DomainTerm> indexSet);

    /**
     * Returns an <code>SExpression</code> representing the body of the macro.
     * 
     * @return an <code>SExpression</code> representing the body of the macro.
     */
    public abstract SExpression getBodyExpression();

    /**
     * Returns the type of this macro.
     * 
     * @return the type of this macro.
     */
    public abstract SExpression getType();

    /**
     * Creates a define-fun expression for this macro.
     * 
     * @return a define-fun expression for this macro.
     */
    public SExpression toSmtlibV2() {
        SExpression result = new SExpression();

        result.addChild(SExpressionConstants.DEFINE_FUN);
        result.addChild(name);
        SExpression allParametersExpression = new SExpression();
        for (Token currentParam : parameters) {
            SExpression currentParamExpression = new SExpression();
            currentParamExpression.addChild(currentParam);
            currentParamExpression.addChild(paramMap.get(currentParam));
            allParametersExpression.addChild(currentParamExpression);
        }

        result.addChild(allParametersExpression);

        result.addChild(getType());

        result.addChild(getBodyExpression());

        return result;
    }
    
    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    public abstract Set<Integer> getAssertPartition();

}
