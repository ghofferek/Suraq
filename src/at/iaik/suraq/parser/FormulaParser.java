/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import at.iaik.suraq.exceptions.NotATokenListException;
import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.formula.ArrayVariable;
import at.iaik.suraq.formula.DomainVariable;
import at.iaik.suraq.formula.Formula;
import at.iaik.suraq.formula.PropositionalVariable;
import at.iaik.suraq.formula.UninterpretedFunction;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class FormulaParser extends Parser {

    /**
     * The formula that results from parsing.
     */
    private Formula formula;

    /**
     * The list of control variables found during parsing
     */
    private final List<PropositionalVariable> controlVariables = new ArrayList<PropositionalVariable>();

    /**
     * The list of Boolean variables found during parsing
     */
    private final List<PropositionalVariable> boolVariables = new ArrayList<PropositionalVariable>();

    /**
     * The list of domain variables found during parsing
     */
    private final List<DomainVariable> domainVariables = new ArrayList<DomainVariable>();

    /**
     * The list of array variables found during parsing
     */
    private final List<ArrayVariable> arrayVariables = new ArrayList<ArrayVariable>();

    /**
     * The list of uninterpreted functions found during parsing
     */
    private final List<UninterpretedFunction> functions = new ArrayList<UninterpretedFunction>();

    /**
     * The root of the s-expression to be parsed.
     */
    private final SExpression rootExpr;

    /**
     * 
     * Constructs a new <code>FormulaParser</code>.
     * 
     * @param root
     *            the root expression to parse.
     */
    public FormulaParser(SExpression root) {
        rootExpr = root;
    }

    /**
     * 
     * @return a (deep) copy of the root expression of this parser.
     */
    public SExpression getRootExpr() {
        return rootExpr.deepCopy();
    }

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

            if (token.equalsString("declare-fun")) {
                handleDeclareFun(expression);
                continue;
            }

            if (token.equalsString("define-fun")) {
                handleDefineFun(expression);
                continue;
            }

            if (token.equalsString("assert")) {
                handleAssert(expression);
                continue;
            }

            // we got something unexpected, if we reach this point.
            throw new ParseError(expression.getLineNumber(),
                    expression.getColumnNumber(), expression.toString(),
                    "Expected 'declare-fun', 'define-fun', or 'assert' expression.");
        }

        parsingSuccessfull = true;
    }

    /**
     * @param expression
     */
    private void handleAssert(SExpression expression) throws ParseError {
        assert (expression.getChildren().get(0) instanceof Token);
        assert (((Token) expression.getChildren().get(0))
                .equalsString("assert"));
        // TODO Auto-generated method stub

    }

    /**
     * Handles a <code>define-fun</code> expression.
     * 
     * @param expression
     *            the <code>define-fun</code> expression.
     */
    private void handleDefineFun(SExpression expression) throws ParseError {
        assert (expression.getChildren().get(0) instanceof Token);
        assert (((Token) expression.getChildren().get(0))
                .equalsString("define-fun"));

        if (expression.getChildren().size() != 5)
            throw new ParseError(expression,
                    "Expected 5 subexpressions in define-fun expression!");

        assert (expression.getChildren().size() == 5);

        if (!(expression.getChildren().get(1) instanceof Token))
            throw new ParseError(expression,
                    "The first argument of define-fun must be a token!");

        assert (expression.getChildren().get(1) instanceof Token);
        Token name = (Token) expression.getChildren().get(1);
        SExpression type = expression.getChildren().get(3);
        SExpression params = expression.getChildren().get(2);
        Map<Token, SExpression> paramMap = parseDefineFunParams(params);
        checkDefineFunType(type);

    }

    /**
     * Checks the type of a define-fun macro.
     * 
     * @param type
     *            the type to to check.
     * @throws ParseError
     *             if the parameters are invalid.
     */
    private void checkDefineFunType(SExpression type) throws ParseError {
        if (type instanceof Token) {
            Token token_param = (Token) type;
            if (token_param.equalsString("Bool")
                    || token_param.equalsString("Value")) {
                return;
            } else {
                throw new ParseError(token_param, "Unsupported type: "
                        + token_param.toString());
            }
        } else { // expecting an (Array Value Value) now.
            try {
                List<Token> tokenList = type.toTokenList();
                if (tokenList.size() != 3)
                    throw new ParseError(type, "Unsupported parameter: "
                            + type.toString());
                if (!(tokenList.get(0).equalsString("Array")
                        && tokenList.get(1).equalsString("Value") && tokenList
                        .get(2).equalsString("Value")))
                    throw new ParseError(type, "Unsupported parameter: "
                            + type.toString());
                else
                    return;
            } catch (NotATokenListException exc) {
                throw new ParseError(type, "Unsupported parameter: "
                        + type.toString(), exc);
            }
        }
    }

    /**
     * Parses the parameters of a define-fun macro.
     * 
     * @param params
     *            the parameters to to check.
     * @return a <code>Map</code> of parameter names (<code>Token</code>s) to
     *         types (<code>SExpression</code>s).
     * @throws ParseError
     *             if the parameters are invalid.
     */
    private Map<Token, SExpression> parseDefineFunParams(SExpression params)
            throws ParseError {
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
            if (paramType instanceof Token) {
                Token token_param = (Token) paramType;
                if (token_param.equalsString("Bool")
                        || token_param.equalsString("Control")
                        || token_param.equalsString("Value")) {
                    paramMap.put((Token) paramName, paramType);
                    continue;
                } else {
                    throw new ParseError(token_param, "Unsupported parameter: "
                            + token_param.toString());
                }
            } else { // expecting an (Array Value Value) now.
                try {
                    List<Token> tokenList = paramType.toTokenList();
                    if (tokenList.size() != 3)
                        throw new ParseError(paramType,
                                "Unsupported parameter: "
                                        + paramType.toString());
                    if (!(tokenList.get(0).equalsString("Array")
                            && tokenList.get(1).equalsString("Value") && tokenList
                            .get(2).equalsString("Value")))
                        throw new ParseError(paramType,
                                "Unsupported parameter: "
                                        + paramType.toString());
                    else
                        paramMap.put((Token) paramName, paramType);
                    continue;
                } catch (NotATokenListException exc) {
                    throw new ParseError(paramType, "Unsupported parameter: "
                            + paramType.toString(), exc);
                }
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

        if (expression.getChildren().size() != 4)
            throw new ParseError(expression,
                    "Expected 4 subexpressions in declare-fun expression!");

        assert (expression.getChildren().size() == 4);

        if (!(expression.getChildren().get(1) instanceof Token))
            throw new ParseError(expression,
                    "The first argument of declare-fun must be a token!");

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
            handleVariable(name, type);
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
            if (!(token.equalsString("Value")))
                throw new ParseError(token, "Unsupported function argument: "
                        + token.toString());
        }
        if (!(type instanceof Token))
            throw new ParseError(type, "Unsupported function type: "
                    + type.toString());
        assert (type instanceof Token);

        functions.add(new UninterpretedFunction(name, param_list.size()));
    }

    /**
     * Handles declarations of new variables (and constants). They must be of
     * one of the following types: Control, Bool, Value, (Array Value Value).
     * 
     * @param name
     *            the name of the variable.
     * @param type
     *            the s-expression determining the type of the variable.
     */
    private void handleVariable(Token name, SExpression type) throws ParseError {

        if (type instanceof Token) { // Control, Bool, or Value
            if (((Token) type).equalsString("Control")) {
                controlVariables.add(new PropositionalVariable(name));
            } else if (((Token) type).equalsString("Bool")) {
                boolVariables.add(new PropositionalVariable(name));
            } else if (((Token) type).equalsString("Value")) {
                domainVariables.add(new DomainVariable(name));
            } else {
                throw new ParseError(type, "Unsupported variable type: "
                        + type.toString());
            }
        }

        try {
            List<Token> token_list = type.toTokenList();
            if (token_list.size() != 3)
                throw new ParseError(type, "Unsupported variable type: "
                        + type.toString());
            if (!(token_list.get(0).equalsString("Array")))
                throw new ParseError(type, "Unsupported variable type: "
                        + type.toString());
            if (!(token_list.get(1).equalsString("Value") && token_list.get(2)
                    .equalsString("Value")))
                throw new ParseError(type, "Unsupported array type: "
                        + type.toString());

            // valid array variable detected
            arrayVariables.add(new ArrayVariable(name));

        } catch (NotATokenListException exc) {
            throw new ParseError(type, "Unsupported variable type: "
                    + type.toString(), exc);
        }

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
        if (child.getChildren().size() != 2)
            throw new ParseError(child.getLineNumber(),
                    child.getColumnNumber(), child.toString(),
                    "Expected '(set-logic Suraq)'.");
        if (!(child.getChildren().get(0) instanceof Token && child
                .getChildren().get(1) instanceof Token))
            throw new ParseError(child.getLineNumber(),
                    child.getColumnNumber(), child.toString(),
                    "Expected '(set-logic Suraq)'.");
        if (!(((Token) child.getChildren().get(0)).equalsString("set-logic") && ((Token) child
                .getChildren().get(1)).equalsString("Suraq")))
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
    public Formula getFormula() {
        if (!wasParsingSuccessfull())
            return null;
        return formula;
    }

    /**
     * Returns a copy of the list of control variables.
     * 
     * @return a copy of the <code>controlVariables</code>
     */
    public List<PropositionalVariable> getControlVariables() {
        return new ArrayList<PropositionalVariable>(controlVariables);
    }

    /**
     * Returns a copy of the list of Boolean variables.
     * 
     * @return a copy of the <code>boolVariables</code>
     */
    public List<PropositionalVariable> getBoolVariables() {
        return new ArrayList<PropositionalVariable>(boolVariables);
    }

    /**
     * Returns a copy of the list of domain variables.
     * 
     * @return a copy of the <code>domainVariables</code>
     */
    public List<DomainVariable> getDomainVariables() {
        return new ArrayList<DomainVariable>(domainVariables);
    }

    /**
     * Returns a copy of the list of array variables.
     * 
     * @return a copy of the <code>arrayVariables</code>
     */
    public List<ArrayVariable> getArrayVariables() {
        return new ArrayList<ArrayVariable>(arrayVariables);
    }

    /**
     * Returns a copy of the list of uninterpreted functions.
     * 
     * @return a copy of the <code>functions</code>
     */
    public List<UninterpretedFunction> getFunctions() {
        return new ArrayList<UninterpretedFunction>(functions);
    }

}
