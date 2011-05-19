/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.parser;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.exceptions.NotATokenListException;
import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.formula.ArrayVariable;
import at.iaik.suraq.formula.DomainVariable;
import at.iaik.suraq.formula.Formula;
import at.iaik.suraq.formula.PropositionalVariable;
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
    private List<PropositionalVariable> controlVariables = new ArrayList<PropositionalVariable>();

    /**
     * The list of Boolean variables found during parsing
     */
    private List<PropositionalVariable> boolVariables = new ArrayList<PropositionalVariable>();

    /**
     * The list of domain variables found during parsing
     */
    private List<DomainVariable> domainVariables = new ArrayList<DomainVariable>();

    /**
     * The list of array variables found during parsing
     */
    private List<ArrayVariable> arrayVariables = new ArrayList<ArrayVariable>();

    /**
     * The root of the s-expression to be parsed.
     */
    private SExpression rootExpr;

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
    private void handleAssert(SExpression expression) {
        // TODO Auto-generated method stub

    }

    /**
     * @param expression
     */
    private void handleDefineFun(SExpression expression) {
        // TODO Auto-generated method stub

    }

    /**
     * Handles a <code>declare-fun</code> expression.
     * 
     * @param expression
     *            the <code>declare-fun</code> expression.
     */
    private void handleDeclareFun(SExpression expression) throws ParseError {
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
     * @param name
     * @param param_list
     * @param type
     */
    private void handleFunction(Token name, List<Token> param_list,
            SExpression type) {
        // TODO Auto-generated method stub

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
                // TODO
            } else if (((Token) type).equalsString("Value")) {
                // TODO
            } else {
                throw new ParseError(type, "Unsupported Variable type: "
                        + type.toString());
            }
        }

        // TODO handle (Array Value Value)

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

}
