/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.parser;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.InvalidParametersException;
import at.iaik.suraq.exceptions.NotATokenListException;
import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.PropositionalFunctionMacro;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.TermFunctionMacro;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class LogicParser extends SMTLibParser implements Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;
    /**
     * The formula that results from parsing.
     */
    protected Formula mainFormula = null;

    /**
     * 
     * Constructs a new <code>FormulaParser</code>.
     * 
     * @param root
     *            the root expression to parse.
     */
    public LogicParser(SExpression root) {
        rootExpr = root;
    }

    // /**
    // *
    // * @return a (deep) copy of the root expression of this parser.
    // */
    // public SExpression getRootExpr() {
    // return rootExpr.deepCopy();
    // }

    /**
     * Parses the root s-expression into a formula, which can then be retrieved
     * using <code>getFormula</code>.
     * 
     * @see at.iaik.suraq.parser.Parser#parse()
     */
    @Override
    public void parse() throws ParseError {

        checkLogic();

        for (int count = 1; count < rootExpr.getChildren().size(); count++) {
            SExpression expression = rootExpr.getChildren().get(count);

            if (expression instanceof Token)
                throw new ParseError(expression.getLineNumber(),
                        expression.getColumnNumber(), expression.toString(),
                        "Unexpected Token.");

            if (expression.getChildren().size() == 0)
                throw new ParseError(expression.getLineNumber(),
                        expression.getColumnNumber(), expression.toString(),
                        "Unexpected empty expression.");

            assert (expression.getChildren().size() >= 1);

            // at this point, we expect a declare-fun, a define-fun, or an
            // assert

            if (!(expression.getChildren().get(0) instanceof Token))
                throw new ParseError(expression.getLineNumber(),
                        expression.getColumnNumber(), expression.toString(),
                        "Expected 'declare-fun', 'define-fun', or 'assert' expression.");

            assert (expression.getChildren().get(0) instanceof Token);
            Token token = (Token) expression.getChildren().get(0);

            if (token.equals(SExpressionConstants.DECLARE_FUN)) {
                handleDeclareFun(expression);
                continue;
            }

            if (token.equals(SExpressionConstants.DEFINE_FUN)) {
                handleDefineFun(expression);
                continue;
            }

            if (token.equals(SExpressionConstants.ASSERT)) {
                handleAssert(expression);
                continue;
            }

            // we got something unexpected, if we reach this point.
            throw new ParseError(expression.getLineNumber(),
                    expression.getColumnNumber(), expression.toString(),
                    "Expected 'declare-fun', 'define-fun', or 'assert' expression.");
        }

        parsingSuccessfull = true;
        rootExpr = null; // Allow this to be garbage collected
    }

    /**
     * Handles an assert expression. I.e., if <code>mainFormula</code> is still
     * <code>null</code>, it will be initialized to the result of parsing this
     * assert statement's body. If <code>mainFormula</code> already is non-
     * <code>null</code>, a conjunction of its current value an the parsed body
     * will be made.
     * 
     * @param expression
     *            the assert expression to parse.
     */
    private void handleAssert(SExpression expression) throws ParseError {
        assert (expression.getChildren().get(0) instanceof Token);
        assert (expression.getChildren().get(0)
                .equals(SExpressionConstants.ASSERT));

        if (expression.getChildren().size() != 2)
            throw new ParseError(expression,
                    "Expected exactly one argument for 'assert'.");

        Formula body = parseFormulaBody(expression.getChildren().get(1));

        if (mainFormula == null)
            mainFormula = body;
        else {
            List<Formula> list = new ArrayList<Formula>();
            list.add(mainFormula);
            list.add(body);
            mainFormula = AndFormula.generate(list);
        }

    }

    /**
     * Handles a <code>define-fun</code> expression.
     * 
     * @param expression
     *            the <code>define-fun</code> expression.
     */
    private void handleDefineFun(SExpression expression) throws ParseError {
        assert (expression.getChildren().get(0) instanceof Token);
        assert (expression.getChildren().get(0)
                .equals(SExpressionConstants.DEFINE_FUN));

        if (expression.getChildren().size() != 5)
            throw new ParseError(expression,
                    "Expected 5 subexpressions in define-fun expression!");

        assert (expression.getChildren().size() == 5);

        if (!(expression.getChildren().get(1) instanceof Token))
            throw new ParseError(expression,
                    "The first argument of define-fun must be a token!");

        assert (expression.getChildren().get(1) instanceof Token);
        Token name = (Token) expression.getChildren().get(1);
        if (name.toString().endsWith("NNF"))
            throw new ParseError(name,
                    "Names of function macros may not end with 'NNF'.");

        SExpression type = expression.getChildren().get(3);
        SExpression params = expression.getChildren().get(2);
        List<Token> paramsList = new ArrayList<Token>();
        Map<Token, SExpression> paramMap;
        try {
            paramMap = parseDefineFunParams(params, paramsList);
        } catch (InvalidParametersException exc) {
            throw new RuntimeException(
                    "Unexpected situation while parsing macro parameters", exc);
        }
        if (type.equals(SExpressionConstants.BOOL_TYPE)) {
            // Handle Bool macro
            Formula body;
            this.currentLocals = paramMap;
            try {
                body = parseFormulaBody(expression.getChildren().get(4));
            } finally {
                this.currentLocals = null;
            }

            PropositionalFunctionMacro macro;
            try {
                macro = PropositionalFunctionMacro.create(name, paramsList,
                        paramMap, body);
            } catch (InvalidParametersException exc) {
                throw new RuntimeException(
                        "Unexpected situation while parsing macro parameters",
                        exc);
            }
            if (macros.containsKey(name))
                throw new ParseError(name, "Duplicate macro definition: "
                        + name.toString());
            else
                macros.put(name, macro);
        } else if (type.equals(SExpressionConstants.VALUE_TYPE)
                || type.equals(SExpressionConstants.ARRAY_TYPE)) {
            // Handle Term macro
            Term body;
            this.currentLocals = paramMap;
            try {
                body = parseTerm(expression.getChildren().get(4));
            } finally {
                this.currentLocals = null;
            }

            TermFunctionMacro macro;
            try {
                macro = TermFunctionMacro.create(name, paramsList, paramMap,
                        body);
            } catch (InvalidParametersException exc) {
                throw new RuntimeException(
                        "Unexpected situation while parsing macro parameters",
                        exc);
            }
            if (macros.containsKey(name))
                throw new ParseError(name, "Duplicate macro definition: "
                        + name.toString());
            else
                macros.put(name, macro);
        } else {
            // Only Bool, Value, and (Array Value Value) macros are allowed
            throw new ParseError(type, "Unsupported type: " + type.toString());
        }

    }

    /**
     * Parses the parameters of a define-fun macro.
     * 
     * @param params
     *            the parameters to to check.
     * @param paramsList
     *            an (empty) list to which the parameter names are added in
     *            order.
     * @return a <code>Map</code> of parameter names (<code>Token</code>s) to
     *         types (<code>SExpression</code>s).
     * @throws ParseError
     *             if the parameters are invalid.
     * @throws InvalidParametersException
     *             if the given <code>paramsList</code> is non-empty or
     *             <code>null</code>;
     */
    private Map<Token, SExpression> parseDefineFunParams(SExpression params,
            List<Token> paramsList) throws ParseError,
            InvalidParametersException {

        if (paramsList == null)
            throw new InvalidParametersException("paramsList is null");
        if (paramsList.size() != 0)
            throw new InvalidParametersException("paramsList is non-empty");

        Map<Token, SExpression> paramMap = new HashMap<Token, SExpression>();
        for (SExpression paramMapping : params.getChildren()) {
            if (paramMapping.getChildren().size() != 2)
                throw new ParseError(paramMapping,
                        "Illegal parameter declaration: "
                                + paramMapping.toString());
            SExpression paramName = paramMapping.getChildren().get(0);
            if (!(paramName instanceof Token))
                throw new ParseError(paramName,
                        "Illegal parameter declaration: "
                                + paramName.toString());
            SExpression paramType = paramMapping.getChildren().get(1);
            if (paramType.equals(SExpressionConstants.BOOL_TYPE)
                    || paramType.equals(SExpressionConstants.VALUE_TYPE)
                    || paramType.equals(SExpressionConstants.ARRAY_TYPE)) {
                paramMap.put((Token) paramName, paramType);
                paramsList.add((Token) paramName);
                continue;
            } else {
                throw new ParseError(paramType, "Unsupported parameter type: "
                        + paramType.toString());
            }
        }
        return paramMap;
    }

    /**
     * Handles a <code>declare-fun</code> expression.
     * 
     * @param expression
     *            the <code>declare-fun</code> expression.
     */
    private void handleDeclareFun(SExpression expression) throws ParseError {

        assert (expression.getChildren().get(0) instanceof Token);
        assert (((Token) expression.getChildren().get(0))
                .equalsString("declare-fun"));

        if (expression.getChildren().size() < 4
                || expression.getChildren().size() > 5)
            throw new ParseError(expression,
                    "Expected 4 or 5 subexpressions in declare-fun expression!");

        assert (expression.getChildren().size() == 4 || expression
                .getChildren().size() == 5);

        if (!(expression.getChildren().get(1) instanceof Token))
            throw new ParseError(expression,
                    "The first argument of declare-fun must be a token!");

        boolean noDependence = false;
        if (expression.getChildren().size() == 5) {
            if (!expression.getChildren().get(4)
                    .equals(SExpressionConstants.NO_DEPENDENCE))
                throw new ParseError(expression.getChildren().get(4),
                        "Expected either '' or ':no_dependence' as fourth parameter of declare-fun.");
            else
                noDependence = true;
        }

        assert (expression.getChildren().get(1) instanceof Token);
        Token name = (Token) expression.getChildren().get(1);
        SExpression type = expression.getChildren().get(3);
        SExpression params = expression.getChildren().get(2);
        List<Token> param_list;
        try {
            param_list = params.toTokenList();
        } catch (NotATokenListException exc) {
            throw new ParseError(params,
                    "Error in parsing argument list of declare-fun!", exc);
        }

        if (param_list.size() == 0)
            handleVariable(name, type, noDependence);
        else
            handleFunction(name, param_list, type);
    }

    /**
     * Handles the declaration of a new uninterpreted function. Only functions
     * of the form <code>(Value+) -> Value</code> are supported.
     * 
     * @param name
     *            the name of the function
     * @param param_list
     *            the parameter list
     * @param type
     *            the return type.
     */
    private void handleFunction(Token name, List<Token> param_list,
            SExpression type) throws ParseError {
        for (Token token : param_list) {
            if (!(token.equals(SExpressionConstants.VALUE_TYPE)))
                throw new ParseError(token, "Unsupported function argument: "
                        + token.toString());
        }
        if (!(type.equals(SExpressionConstants.VALUE_TYPE) || type
                .equals(SExpressionConstants.BOOL_TYPE)))
            throw new ParseError(type, "Unsupported function type: "
                    + type.toString());
        assert (type instanceof Token);

        if (!functions.add(UninterpretedFunction.create(name,
                param_list.size(), (Token) type))) {
            throw new ParseError(name, "Duplicate function definition: "
                    + name.toString());
        }
    }

    /**
     * Handles declarations of new variables (and constants). They must be of
     * one of the following types: Control, Bool, Value, (Array Value Value).
     * 
     * @param name
     *            the name of the variable.
     * @param type
     *            the s-expression determining the type of the variable.
     * @param noDependence
     *            <code>true</code> if this is a variable on which control logic
     *            may <em>not</em> depend.
     */
    private void handleVariable(Token name, SExpression type,
            boolean noDependence) throws ParseError {

        if (checkNameExists(name)) {
            throw new ParseError(name, "Name already used: " + name.toString());
            // After this check the exceptions below should actually never
            // be thrown.
        }

        if (type.equals(SExpressionConstants.CONTROL_TYPE)) {
            if (!controlVariables.add(PropositionalVariable.create(name))) {
                throw new ParseError(name, "Duplicate variable definition: "
                        + name.toString());
            }
        } else if (type.equals(SExpressionConstants.BOOL_TYPE)) {
            if (!boolVariables.add(PropositionalVariable.create(name))) {
                throw new ParseError(name, "Duplicate variable definition: "
                        + name.toString());
            }
        } else if (type.equals(SExpressionConstants.VALUE_TYPE)) {
            if (!domainVariables.add(DomainVariable.create(name))) {
                throw new ParseError(name, "Duplicate variable definition: "
                        + name.toString());
            }
        } else if (type.equals(SExpressionConstants.ARRAY_TYPE)) {
            if (!arrayVariables.add(ArrayVariable.create(name))) {
                throw new ParseError(name, "Duplicate variable definition: "
                        + name.toString());
            }
        } else {
            throw new ParseError(type, "Unsupported variable type: "
                    + type.toString());
        }

        if (noDependence) {
            noDependenceVariables.add(name);
        }

    }

    /**
     * Checks whether the given name already exists (as an identifier of any
     * other type).
     * 
     * @param name
     *            the name to check.
     * @return <code>true</code> if something with this name already exists,
     *         false otherwise.
     */
    private boolean checkNameExists(Token name) {
        Set<Token> names = new HashSet<Token>();

        for (PropositionalVariable variable : boolVariables)
            names.add(Token.generate(variable.getVarName()));

        for (PropositionalVariable variable : controlVariables)
            names.add(Token.generate(variable.getVarName()));

        for (DomainVariable variable : domainVariables)
            names.add(Token.generate(variable.getVarName()));

        for (ArrayVariable variable : arrayVariables)
            names.add(Token.generate(variable.getVarName()));

        for (UninterpretedFunction function : functions)
            names.add(function.getName());

        names.addAll(macros.keySet());

        return names.contains(names);
    }

    /**
     * Check if the first child of the root expression is
     * <code>(set-logic Suraq)</code>
     * 
     * @throws ParseError
     *             if the first child of the root expression is not
     *             <code>(set-logic Suraq)</code>
     */
    private void checkLogic() throws ParseError {
        assert (rootExpr.getChildren() != null);
        if (rootExpr.getChildren().size() < 1)
            throw new ParseError("Empty input");
        SExpression child = rootExpr.getChildren().get(0);
        if (!child.equals(SExpressionConstants.SET_LOGIC_SURAQ))
            throw new ParseError(child.getLineNumber(),
                    child.getColumnNumber(), child.toString(),
                    "Expected '(set-logic Suraq)'.");
    }

    /**
     * Returns the formula that resulted from parsing, or <code>null</code> if
     * parsing was not successful.
     * 
     * @return the formula that resulted from parsing, or <code>null</code> if
     *         parsing was not successful.
     */
    public Formula getMainFormula() {
        if (!wasParsingSuccessfull())
            return null;
        return mainFormula;
    }

}
