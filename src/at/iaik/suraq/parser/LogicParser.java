/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.parser;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.IncomparableTermsException;
import at.iaik.suraq.exceptions.InvalidIndexGuardException;
import at.iaik.suraq.exceptions.InvalidParametersException;
import at.iaik.suraq.exceptions.InvalidValueConstraintException;
import at.iaik.suraq.exceptions.NotATokenListException;
import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.exceptions.WrongNumberOfParametersException;
import at.iaik.suraq.formula.AndFormula;
import at.iaik.suraq.formula.ArrayIte;
import at.iaik.suraq.formula.ArrayProperty;
import at.iaik.suraq.formula.ArrayRead;
import at.iaik.suraq.formula.ArrayTerm;
import at.iaik.suraq.formula.ArrayVariable;
import at.iaik.suraq.formula.ArrayWrite;
import at.iaik.suraq.formula.DomainIte;
import at.iaik.suraq.formula.DomainTerm;
import at.iaik.suraq.formula.DomainVariable;
import at.iaik.suraq.formula.EqualityFormula;
import at.iaik.suraq.formula.Formula;
import at.iaik.suraq.formula.FunctionMacro;
import at.iaik.suraq.formula.FunctionMacroInstance;
import at.iaik.suraq.formula.ImpliesFormula;
import at.iaik.suraq.formula.NotFormula;
import at.iaik.suraq.formula.OrFormula;
import at.iaik.suraq.formula.PropositionalConstant;
import at.iaik.suraq.formula.PropositionalIte;
import at.iaik.suraq.formula.PropositionalVariable;
import at.iaik.suraq.formula.Term;
import at.iaik.suraq.formula.UninterpretedFunction;
import at.iaik.suraq.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.formula.XorFormula;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class LogicParser extends Parser {

    /**
     * The formula that results from parsing.
     */
    private Formula mainFormula = null;

    /**
     * The list of control variables found during parsing
     */
    private final Set<PropositionalVariable> controlVariables = new HashSet<PropositionalVariable>();

    /**
     * The list of Boolean variables found during parsing
     */
    private final Set<PropositionalVariable> boolVariables = new HashSet<PropositionalVariable>();

    /**
     * The list of domain variables found during parsing
     */
    private final Set<DomainVariable> domainVariables = new HashSet<DomainVariable>();

    /**
     * The list of array variables found during parsing
     */
    private final Set<ArrayVariable> arrayVariables = new HashSet<ArrayVariable>();

    /**
     * The list of uninterpreted functions found during parsing
     */
    private final Set<UninterpretedFunction> functions = new HashSet<UninterpretedFunction>();

    /**
     * The function macros found during parsing, indexed by name tokens
     */
    private final Map<Token, FunctionMacro> macros = new HashMap<Token, FunctionMacro>();

    /**
     * The root of the s-expression to be parsed.
     */
    private final SExpression rootExpr;

    /**
     * A map of current local variables while parsing a function macro.
     */
    private Map<Token, SExpression> currentLocals = null;

    /**
     * The set of universally quantified variables in current scope.
     */
    private Collection<DomainVariable> currentUVars = null;

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
            mainFormula = new AndFormula(list);
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
        if (!type.equals(SExpressionConstants.BOOL_TYPE)) {
            // Only Bool macros allowed at this time
            throw new ParseError(type, "Unsupported type: " + type.toString());
        }
        Formula body;
        this.currentLocals = paramMap;
        try {
            body = parseFormulaBody(expression.getChildren().get(4));
        } finally {
            this.currentLocals = null;
        }

        FunctionMacro macro;
        try {
            macro = new FunctionMacro(name, paramsList, paramMap, body);
        } catch (InvalidParametersException exc) {
            throw new RuntimeException(
                    "Unexpected situation while parsing macro parameters", exc);
        }
        if (macros.containsKey(name))
            throw new ParseError(name, "Duplicate macro definition: "
                    + name.toString());
        else
            macros.put(name, macro);

    }

    /**
     * Parses a given s-expression into a formula.
     * 
     * @param expression
     *            the expression to parse.
     * @return the formula resulting from the given expression.
     * @throws ParseError
     *             if parsing fails.
     */
    private Formula parseFormulaBody(SExpression expression) throws ParseError {

        if (isPropositionalConstant(expression)) {
            PropositionalConstant constant = null;
            if (expression.equals(SExpressionConstants.TRUE))
                constant = new PropositionalConstant(true);
            else if (expression.equals(SExpressionConstants.FALSE))
                constant = new PropositionalConstant(false);
            else
                throw new ParseError(expression,
                        "Unexpected Error parsing propositional constant!");
            return constant;
        }

        if (isPropositionalVariable(expression)) {
            return new PropositionalVariable((Token) expression);
        }

        Token operator = isBooleanCombination(expression);
        if (operator != null) {
            if (operator.equals(SExpressionConstants.NOT)) {
                if (expression.getChildren().size() != 2)
                    throw new ParseError(expression,
                            "Expected exactly 1 expression after 'not'.");
                Formula negatedFormula = parseFormulaBody(expression
                        .getChildren().get(1));
                return new NotFormula(negatedFormula);
            }

            if (operator.equals(SExpressionConstants.AND)) {
                if (expression.getChildren().size() < 3)
                    throw new ParseError(expression,
                            "Expected at least 2 expression after 'and'.");
                List<Formula> formulaList = new ArrayList<Formula>();
                for (SExpression child : expression.getChildren().subList(1,
                        expression.getChildren().size())) {
                    formulaList.add(parseFormulaBody(child));
                }
                return new AndFormula(formulaList);
            }

            if (operator.equals(SExpressionConstants.OR)) {
                if (expression.getChildren().size() < 3)
                    throw new ParseError(expression,
                            "Expected at least 2 expression after 'or'.");
                List<Formula> formulaList = new ArrayList<Formula>();
                for (SExpression child : expression.getChildren().subList(1,
                        expression.getChildren().size())) {
                    formulaList.add(parseFormulaBody(child));
                }
                return new OrFormula(formulaList);
            }

            if (operator.equals(SExpressionConstants.XOR)) {
                if (expression.getChildren().size() < 3)
                    throw new ParseError(expression,
                            "Expected at least 2 expression after 'xor'.");
                List<Formula> formulaList = new ArrayList<Formula>();
                for (SExpression child : expression.getChildren().subList(1,
                        expression.getChildren().size())) {
                    formulaList.add(parseFormulaBody(child));
                }
                return new XorFormula(formulaList);
            }

            if (operator.equals(SExpressionConstants.IMPLIES)) {
                if (expression.getChildren().size() != 3)
                    throw new ParseError(expression,
                            "Expected 2 arguments for '=>'.");
                Formula leftSide = parseFormulaBody(expression.getChildren()
                        .get(1));
                Formula rightSide = parseFormulaBody(expression.getChildren()
                        .get(2));
                return new ImpliesFormula(leftSide, rightSide);
            }

            if (operator.equals(SExpressionConstants.ITE)) {
                if (expression.getChildren().size() != 4)
                    throw new ParseError(expression,
                            "Expected 3 arguments for 'ite'.");
                Formula condition = parseFormulaBody(expression.getChildren()
                        .get(1));
                Formula thenBranch = parseFormulaBody(expression.getChildren()
                        .get(2));
                Formula elseBranch = parseFormulaBody(expression.getChildren()
                        .get(3));
                return new PropositionalIte(condition, thenBranch, elseBranch);
            }
            throw new ParseError(expression, "Unexpected internal parse error!");

        }

        if (isEquality(expression)) {
            assert (expression.getChildren().size() >= 3);
            boolean equal;
            if (expression.getChildren().get(0)
                    .equals(SExpressionConstants.EQUAL))
                equal = true;
            else if (expression.getChildren().get(0)
                    .equals(SExpressionConstants.DISTINCT))
                equal = false;
            else
                throw new ParseError(expression,
                        "Unexpected internal parse error!");

            List<Term> termList = new ArrayList<Term>();
            for (SExpression child : expression.getChildren().subList(1,
                    expression.getChildren().size())) {
                termList.add(parseTerm(child));
            }

            try {
                return EqualityFormula.create(termList, equal);
            } catch (IncomparableTermsException exc) {
                throw new ParseError(expression,
                        "Incomparable terms in equality.", exc);
            }
        }

        if (isArrayProperty(expression)) {
            if (expression.getChildren().size() != 3)
                throw new ParseError(expression,
                        "Expected 2 arguments for 'forall' expression.");
            assert (expression.getChildren().get(0)
                    .equals(SExpressionConstants.FORALL));
            SExpression uVarsExpression = expression.getChildren().get(1);
            try {
                currentUVars = parseUVars(uVarsExpression);
                SExpression property = expression.getChildren().get(2);
                Formula indexGuard;
                Formula valueConstraint;
                if (property.getChildren().size() <= 2) { // not an implication
                    indexGuard = new PropositionalConstant(true);
                    valueConstraint = parseFormulaBody(property);
                } else if (!property.getChildren().get(0)
                        .equals(SExpressionConstants.IMPLIES)) {
                    // also not an implication
                    indexGuard = new PropositionalConstant(true);
                    valueConstraint = parseFormulaBody(property);
                } else { // we have an implication
                    if (property.getChildren().size() != 3)
                        throw new ParseError(property,
                                "Malformed array property!");
                    assert (property.getChildren().get(0)
                            .equals(SExpressionConstants.IMPLIES));
                    indexGuard = parseFormulaBody(property.getChildren().get(1));
                    valueConstraint = parseFormulaBody(property.getChildren()
                            .get(2));
                }

                try {
                    return new ArrayProperty(currentUVars, indexGuard,
                            valueConstraint);
                } catch (InvalidIndexGuardException exc) {
                    throw new ParseError(property, "Malformed index guard.",
                            exc);
                } catch (InvalidValueConstraintException exc) {
                    throw new ParseError(property,
                            "Malformed value constraint.", exc);
                }

            } finally {
                currentUVars = null;
            }
        }

        FunctionMacro macro = isMacroInstance(expression);
        if (macro != null) {
            List<SExpression> paramExpressions = expression.getChildren()
                    .subList(1, expression.getChildren().size());
            if (paramExpressions.size() != macro.getNumParams())
                throw new ParseError(expression, "Expected "
                        + macro.getNumParams() + "parameters for macro "
                        + macro.getName().toString() + ", got "
                        + paramExpressions.size() + " instead.");

            Map<Token, Term> paramMap = new HashMap<Token, Term>();
            assert (paramExpressions.size() != macro.getNumParams());
            for (int count = 0; count < paramExpressions.size(); count++) {
                Term paramTerm = parseTerm(paramExpressions.get(count));

                if (!paramTerm.getType().equals(macro.getParamType(count)))
                    throw new ParseError(paramExpressions.get(count),
                            "Wrong parameter type. Expected "
                                    + macro.getParamType(count).toString()
                                    + ", got " + paramTerm.getType().toString()
                                    + " instead.");

                paramMap.put(macro.getParam(count), paramTerm);
            }
            try {
                return new FunctionMacroInstance(macro, paramMap);
            } catch (InvalidParametersException exc) {
                throw new RuntimeException(
                        "Unexpected condition while creating function macro.",
                        exc);
            }
        }

        // we have something we cannot handle
        if (expression instanceof Token)
            throw new ParseError(expression, "Undeclared identifier: "
                    + expression.toString());
        else
            throw new ParseError(expression, "Error parsing formula body.");
    }

    /**
     * Parses the list of universally quantified variables.
     * 
     * @param uVarsExpression
     *            the first argument of a <code>forall</code> expression
     * @return the collection of universally quantified variables.
     */
    private Collection<DomainVariable> parseUVars(SExpression uVarsExpression)
            throws ParseError {
        Set<DomainVariable> uVars = new HashSet<DomainVariable>();
        if (uVarsExpression.isEmpty())
            throw new ParseError(uVarsExpression, "Empty variable list.");
        for (SExpression child : uVarsExpression.getChildren()) {
            if (child.getChildren().size() != 2)
                throw new ParseError(child, "Invalid quantified variable");
            if (!child.getChildren().get(1)
                    .equals(SExpressionConstants.VALUE_TYPE))
                throw new ParseError(child.getChildren().get(1),
                        "Invalid type of quantified variable: "
                                + child.getChildren().get(1).toString());
            if (!(child.getChildren().get(0) instanceof Token))
                throw new ParseError(child.getChildren().get(0),
                        "Expected variable name.");
            if (!uVars.add(new DomainVariable((Token) child.getChildren()
                    .get(0)))) {
                throw new ParseError(child.getChildren().get(0),
                        "Duplicate variable in quantifier scope: "
                                + child.getChildren().get(0).toString());
            }
        }
        return uVars;
    }

    /**
     * Parses the given expression as a term.
     * 
     * @param expression
     *            the expression to parse
     * @return the term resulting from parsing.
     * @throws ParseError
     *             if parsing fails
     */
    private Term parseTerm(SExpression expression) throws ParseError {

        if (isUVar(expression)) { // Takes precedence over other variable types
            return new DomainVariable((Token) expression);
        }

        SExpression type = isLocalVariable(expression); // takes precedence over
                                                        // global variables.
        if (type != null) {
            if (type.equals(SExpressionConstants.ARRAY_TYPE)) {
                return new ArrayVariable((Token) expression);
            }
            if (type.equals(SExpressionConstants.VALUE_TYPE)) {
                return new DomainVariable((Token) expression);
            }
            if (type.equals(SExpressionConstants.BOOL_TYPE)
                    || type.equals(SExpressionConstants.CONTROL_TYPE)) {
                return new PropositionalVariable((Token) expression);
            }
            // In case we have a type that should not exist:
            throw new RuntimeException(
                    "Unexpected type while handling local variable: "
                            + type.toString());
        }

        if (isIteTerm(expression)) {
            if (expression.getChildren().size() != 4)
                throw new ParseError(expression,
                        "Expected 3 parameters for 'ite' expression.");
            Formula condition = parseFormulaBody(expression.getChildren()
                    .get(1));
            Term thenBranch = parseTerm(expression.getChildren().get(2));
            Term elseBranch = parseTerm(expression.getChildren().get(3));

            if (thenBranch instanceof ArrayTerm
                    && elseBranch instanceof ArrayTerm)
                return new ArrayIte(condition, (ArrayTerm) thenBranch,
                        (ArrayTerm) elseBranch);

            if (thenBranch instanceof DomainTerm
                    && elseBranch instanceof DomainTerm)
                return new DomainIte(condition, (DomainTerm) thenBranch,
                        (DomainTerm) elseBranch);

            throw new ParseError(expression,
                    "Incompatible types in 'ite' expression");
        }

        if (isArrayVariable(expression)) {
            return new ArrayVariable(expression.toString());
        }

        if (isArrayWrite(expression)) {
            if (expression.getChildren().size() != 4)
                throw new ParseError(expression,
                        "Expected 3 parameters for 'store' expression.");

            Term arrayTerm = parseTerm(expression.getChildren().get(1));
            if (!(arrayTerm instanceof ArrayTerm))
                throw new ParseError(expression.getChildren().get(1),
                        "First parameter of 'store' must be an array term.");

            Term indexTerm = parseTerm(expression.getChildren().get(2));
            if (!(indexTerm instanceof DomainTerm))
                throw new ParseError(expression.getChildren().get(2),
                        "Second parameter of 'store' must be a domain term.");

            Term valueTerm = parseTerm(expression.getChildren().get(3));
            if (!(valueTerm instanceof DomainTerm))
                throw new ParseError(expression.getChildren().get(3),
                        "Third parameter of 'store' must be a domain term.");

            return new ArrayWrite((ArrayTerm) arrayTerm,
                    (DomainTerm) indexTerm, (DomainTerm) valueTerm);
        }

        if (isDomainVariable(expression)) {
            return new DomainVariable(expression.toString());
        }

        UninterpretedFunction function = isUninterpredFunctionInstance(expression);
        if (function != null) {
            if (function.getNumParams() != expression.getChildren().size() - 1)
                throw new ParseError(expression, "Function '"
                        + function.getName() + "' expects "
                        + function.getNumParams() + " parameters.");
            List<DomainTerm> parameters = new ArrayList<DomainTerm>();
            for (int count = 0; count < function.getNumParams(); count++) {
                Term term = parseTerm(expression.getChildren().get(count + 1));
                if (!(term instanceof DomainTerm))
                    throw new ParseError(expression.getChildren()
                            .get(count + 1), "Parameter is not a domain term.");
                parameters.add((DomainTerm) term);
            }
            try {
                return new UninterpretedFunctionInstance(function, parameters);
            } catch (WrongNumberOfParametersException exc) {
                throw new RuntimeException(
                        "Unexpected situation while parsing uninterpreted function instance.");
            }
        }

        if (isArrayRead(expression)) {
            if (expression.getChildren().size() != 3)
                throw new ParseError(expression,
                        "Expected 2 parameters for 'select' expression.");

            Term arrayTerm = parseTerm(expression.getChildren().get(1));
            if (!(arrayTerm instanceof ArrayTerm))
                throw new ParseError(expression.getChildren().get(1),
                        "First parameter of 'select' must be an array term.");

            Term indexTerm = parseTerm(expression.getChildren().get(2));
            if (!(indexTerm instanceof DomainTerm))
                throw new ParseError(expression.getChildren().get(2),
                        "Second parameter of 'select' must be a domain term.");

            return new ArrayRead((ArrayTerm) arrayTerm, (DomainTerm) indexTerm);
        }

        if (isPropositional(expression)) {
            if (expression.equals(SExpressionConstants.TRUE))
                return new PropositionalConstant(true);
            else if (expression.equals(SExpressionConstants.FALSE))
                return new PropositionalConstant(false);

            PropositionalVariable variable = new PropositionalVariable(
                    (Token) expression);
            if (!boolVariables.contains(variable)
                    && !controlVariables.contains(variable))
                throw new RuntimeException(
                        "Unexpected situation while handling variable "
                                + variable.toString());
            return variable;
        }
        // we have something we cannot handle
        throw new ParseError("General parse error while parsing term "
                + expression.toString());
    }

    /**
     * Checks if the given expression is a propositional variable or constant.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the given expression is a propositional
     *         variable or constant, <code>false</code> otherwise.
     */
    private boolean isPropositional(SExpression expression) {
        if (!(expression instanceof Token))
            return false;

        if (expression.equals(SExpressionConstants.TRUE))
            return true;

        if (expression.equals(SExpressionConstants.FALSE))
            return true;

        PropositionalVariable variable = new PropositionalVariable(
                (Token) expression);
        if (boolVariables.contains(variable)
                || controlVariables.contains(variable))
            return true;
        else
            return false;
    }

    /**
     * Checks if the given expression is a universally quantified variable (in
     * current scope).
     * 
     * @param expression
     *            the expression to check
     * @return <code>true</code> if the expression is a universally quantified
     *         variable, <code>false</code> otherwise.
     */
    private boolean isUVar(SExpression expression) {
        if (currentUVars == null)
            return false;

        if (!(expression instanceof Token))
            return false;

        return (this.currentUVars.contains(new DomainVariable(
                (Token) expression)));
    }

    /**
     * Checks if the given expression is a current local variable. Returns the
     * type of the variable, or <code>null</code> if no such variable exists.
     * 
     * @param expression
     *            the expression to check
     * @return the type of the local variable or <code>null</code> if it does
     *         not exist.
     */
    private SExpression isLocalVariable(SExpression expression) {
        if (currentLocals == null)
            return null;

        return currentLocals.get(expression);
    }

    /**
     * Checks if the given expression is an if-then-else term
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the first child of <code>expression</code>
     *         is a <code>Token</code> and it equals the ITE operator.
     */
    private boolean isIteTerm(SExpression expression) {
        if (expression instanceof Token)
            return false;
        if (expression.getChildren().size() < 1)
            return false;
        if (expression.getChildren().get(0).equals(SExpressionConstants.ITE))
            return true;

        return false;
    }

    /**
     * Checks whether the given expression is an array read.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the first child of <code>expression</code>
     *         is the <code>select</code> token, <code>false</code> otherwise.
     */
    private boolean isArrayRead(SExpression expression) {
        if (expression instanceof Token)
            return false;
        if (expression.getChildren().size() < 1)
            return false;

        if (!expression.getChildren().get(0)
                .equals(SExpressionConstants.SELECT))
            return false;
        else
            return true;
    }

    /**
     * Checks whether the given expression is an array write.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the first child of <code>expression</code>
     *         is the <code>store</code> token, <code>false</code> otherwise.
     */
    private boolean isArrayWrite(SExpression expression) {
        if (expression instanceof Token)
            return false;
        if (expression.getChildren().size() < 1)
            return false;

        if (!expression.getChildren().get(0).equals(SExpressionConstants.STORE))
            return false;
        else
            return true;
    }

    /**
     * Checks whether the given expression is an uninterpreted function
     * instance. If so, the function is returned.
     * 
     * @param expression
     *            the expression to check
     * @return if the given expression is an uninterpreted function instance,
     *         the function is returned. Otherwise <code>null</code> is
     *         returned.
     */
    private UninterpretedFunction isUninterpredFunctionInstance(
            SExpression expression) {
        if (expression instanceof Token)
            return null;
        if (expression.getChildren().size() < 2)
            return null;
        if (!(expression.getChildren().get(0) instanceof Token))
            return null;
        Token name = (Token) expression.getChildren().get(0);
        for (UninterpretedFunction function : functions) {
            if (name.equals(function.getName()))
                return function;
        }
        return null;
    }

    /**
     * Checks whether the given expression is a domain variable
     * 
     * @param expression
     *            the expression to check
     * @return <code>true</code> if the given expression is a domain variable,
     *         <code>false</code> otherwise.
     */
    private boolean isDomainVariable(SExpression expression) {
        if (!(expression instanceof Token))
            return false;
        return domainVariables.contains(new DomainVariable((Token) expression));
    }

    /**
     * Checks whether the given expression is an array variable
     * 
     * @param expression
     *            the expression to check
     * @return <code>true</code> if the given expression is an array variable,
     *         <code>false</code> otherwise.
     */
    private boolean isArrayVariable(SExpression expression) {
        if (!(expression instanceof Token))
            return false;
        return arrayVariables.contains(new ArrayVariable((Token) expression));
    }

    /**
     * Checks if the given expression is a macro instance. If so, the
     * corresponding macro is returned.
     * 
     * @param expression
     *            the expression to check.
     * @return the macro instantiated by this expression, or <code>null</code>
     *         if this is not a macro instance
     */
    private FunctionMacro isMacroInstance(SExpression expression) {
        if (expression instanceof Token)
            return null;
        if (expression.getChildren().size() < 2)
            return null;
        if (!(expression.getChildren().get(0) instanceof Token))
            return null;

        assert (expression.getChildren().get(0) instanceof Token);
        Token macroName = (Token) expression.getChildren().get(0);
        return macros.get(macroName);
    }

    /**
     * Checks whether the given expression is an array property. For more
     * meaningful parse errors, everything starting with a <code>forall</code>
     * token is considered an array property here.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the given expression starts with a
     *         <code>forall</code> token.
     */
    private boolean isArrayProperty(SExpression expression) {
        if (expression instanceof Token)
            return false;
        if (expression.getChildren().size() < 1)
            return false;

        SExpression firstChild = expression.getChildren().get(0);
        if (!(firstChild instanceof Token))
            return false;
        if (firstChild.equals(SExpressionConstants.FORALL))
            return true;

        return false;
    }

    /**
     * Checks whether the given expression is an equality instance.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the given expression is an equality
     *         expression, <code>false</code> otherwise.
     */
    private boolean isEquality(SExpression expression) {
        if (expression instanceof Token)
            return false;
        if (expression.getChildren().size() < 3)
            return false;
        if (!(expression.getChildren().get(0) instanceof Token))
            return false;
        assert (expression.getChildren().get(0) instanceof Token);
        Token operator = (Token) expression.getChildren().get(0);

        if (operator.equals(SExpressionConstants.EQUAL)
                || operator.equals(SExpressionConstants.DISTINCT))
            return true;
        return false;
    }

    /**
     * Checks if the given expression is a Boolean combination (excluding
     * equality). If so, its operator is returned. Otherwise, <code>null</code>
     * is returned.
     * 
     * @param expression
     *            the expression to check.
     * @return the operator used, if the given expression is a Boolean
     *         combination (except equality). <code>null</code> otherwise.
     * 
     */
    private Token isBooleanCombination(SExpression expression) {
        if (expression instanceof Token)
            return null;
        if (expression.getChildren().size() < 2)
            return null;
        if (!(expression.getChildren().get(0) instanceof Token))
            return null;

        assert (expression.getChildren().get(0) instanceof Token);
        Token operator = (Token) expression.getChildren().get(0);

        if (operator.equals(SExpressionConstants.AND)
                || operator.equals(SExpressionConstants.OR)
                || operator.equals(SExpressionConstants.XOR)
                || operator.equals(SExpressionConstants.NOT)
                || operator.equals(SExpressionConstants.IMPLIES)
                || operator.equals(SExpressionConstants.ITE))
            return operator;

        return null;
    }

    /**
     * Checks if the given expression is a propositional variable.
     * 
     * @param expression
     *            the expression to check
     * @return <code>true</code> if the given expression is a propositional
     *         variable, <code>false</code> otherwise.
     */
    private boolean isPropositionalVariable(SExpression expression) {
        if (!(expression instanceof Token))
            return false;
        Token token = (Token) expression;
        PropositionalVariable variable = new PropositionalVariable(token);
        if (domainVariables.contains(variable)
                || controlVariables.contains(variable))
            return true;
        else
            return false;
    }

    /**
     * Checks if the given expression is a propositional constant.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the given expression is a propositional
     *         constant, <code>false</code> otherwise.
     */
    private boolean isPropositionalConstant(SExpression expression) {
        return (expression.equals(SExpressionConstants.TRUE) || expression
                .equals(SExpressionConstants.FALSE));
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
            if (!(token.equals(SExpressionConstants.VALUE_TYPE)))
                throw new ParseError(token, "Unsupported function argument: "
                        + token.toString());
        }
        if (!(type.equals(SExpressionConstants.VALUE_TYPE)))
            throw new ParseError(type, "Unsupported function type: "
                    + type.toString());
        assert (type instanceof Token);

        if (!functions.add(new UninterpretedFunction(name, param_list.size()))) {
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
     */
    private void handleVariable(Token name, SExpression type) throws ParseError {

        if (type.equals(SExpressionConstants.CONTROL_TYPE)) {
            if (!controlVariables.add(new PropositionalVariable(name))) {
                throw new ParseError(name, "Duplicate variable definition: "
                        + name.toString());
            }
        } else if (type.equals(SExpressionConstants.BOOL_TYPE)) {
            if (!boolVariables.add(new PropositionalVariable(name))) {
                throw new ParseError(name, "Duplicate variable definition: "
                        + name.toString());
            }
        } else if (type.equals(SExpressionConstants.VALUE_TYPE)) {
            if (!domainVariables.add(new DomainVariable(name))) {
                throw new ParseError(name, "Duplicate variable definition: "
                        + name.toString());
            }
        } else if (type.equals(SExpressionConstants.ARRAY_TYPE)) {
            if (!arrayVariables.add(new ArrayVariable(name))) {
                throw new ParseError(name, "Duplicate variable definition: "
                        + name.toString());
            }
        } else {
            throw new ParseError(type, "Unsupported variable type: "
                    + type.toString());
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

    /**
     * Returns a copy of the list of function macros.
     * 
     * @return a copy of the <code>macros</code>
     */
    public List<FunctionMacro> getMacros() {
        return new ArrayList<FunctionMacro>(macros.values());
    }
}
