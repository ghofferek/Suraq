package at.iaik.suraq.parser;

import java.io.Serializable;
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
import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.ArrayIte;
import at.iaik.suraq.smtlib.formula.ArrayProperty;
import at.iaik.suraq.smtlib.formula.ArrayRead;
import at.iaik.suraq.smtlib.formula.ArrayTerm;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.ArrayWrite;
import at.iaik.suraq.smtlib.formula.DomainIte;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.FormulaTerm;
import at.iaik.suraq.smtlib.formula.FunctionMacro;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.smtlib.formula.PropositionalFunctionMacro;
import at.iaik.suraq.smtlib.formula.PropositionalFunctionMacroInstance;
import at.iaik.suraq.smtlib.formula.PropositionalIte;
import at.iaik.suraq.smtlib.formula.PropositionalTerm;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.TermFunctionMacro;
import at.iaik.suraq.smtlib.formula.TermFunctionMacroInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.smtlib.formula.XorFormula;

public abstract class SMTLibParser extends Parser implements Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * maps containing proof references
     */
    protected final Map<Token, Z3Proof> proofs = new HashMap<Token, Z3Proof>();

    protected final Map<Token, Formula> formulas = new HashMap<Token, Formula>();

    protected final Map<Token, Term> terms = new HashMap<Token, Term>();

    protected final List<PropositionalVariable> tseitinVariables = new ArrayList<PropositionalVariable>();

    private static final int GLOBAL_PARTITION = -1;

    /**
     * constants for let expression types
     */
    public static final char REF_PROOF = '@';
    public static final char REF_FORMULA = '$';
    public static final char REF_TERM = '?';

    /**
     * The list of control variables found during parsing
     */
    protected List<PropositionalVariable> controlVariables = new ArrayList<PropositionalVariable>();

    /**
     * The list of Boolean variables found during parsing
     */
    protected Set<PropositionalVariable> boolVariables = new HashSet<PropositionalVariable>();

    /**
     * The list of domain variables found during parsing
     */
    protected Set<DomainVariable> domainVariables = new HashSet<DomainVariable>();

    /**
     * The list of array variables found during parsing
     */
    protected Set<ArrayVariable> arrayVariables = new HashSet<ArrayVariable>();

    /**
     * The list of uninterpreted functions found during parsing
     */
    protected Set<UninterpretedFunction> functions = new HashSet<UninterpretedFunction>();

    /**
     * The set of variables on which control logic may <em>not</em> depend
     */
    protected Set<Token> noDependenceVariables = new HashSet<Token>();

    /**
     * The function macros found during parsing, indexed by name tokens
     */
    protected Map<Token, FunctionMacro> macros = new HashMap<Token, FunctionMacro>();

    /**
     * The root of the s-expression to be parsed.
     */
    protected SExpression rootExpr = null;

    /**
     * A map of current local variables while parsing a function macro.
     */
    protected Map<Token, SExpression> currentLocals = null;

    /**
     * The set of universally quantified variables in current scope.
     */
    protected Collection<DomainVariable> currentUVars = null;

    protected Map<Token, Formula> letFormulaDefinitions = new HashMap<Token, Formula>();

    protected Map<Token, Term> letTermDefinitions = new HashMap<Token, Term>();

    /**
     * Parses a given s-expression into a formula.
     * 
     * @param expression
     *            the expression to parse.
     * @return the formula resulting from the given expression.
     * @throws ParseError
     *             if parsing fails.
     */
    public Formula parseFormulaBody(SExpression expression) throws ParseError {
        if (isLet(expression))
            return handleLet(expression);

        if (expression.toString().charAt(0) == SMTLibParser.REF_FORMULA) {
            // resolve reference with LUT
            assert (expression instanceof Token);
            Token pureKey = Token.generate(expression.toString().substring(1));
            Formula formula = this.formulas.get(pureKey);

            if (formula == null)
                throw new ParseError(expression,
                        "could not find a matching formula-LUT-entry!");

            return formula;
        }

        if (isPropositionalConstant(expression)) {
            PropositionalConstant constant = null;
            if (expression.equals(SExpressionConstants.TRUE))
                constant = PropositionalConstant.create(true);
            else if (expression.equals(SExpressionConstants.FALSE))
                constant = PropositionalConstant.create(false);
            else
                throw new ParseError(expression,
                        "Unexpected Error parsing propositional constant!");
            return constant;
        }

        SExpression type = isLocalVariable(expression); // takes precedence over
                                                        // global variables.
        if (type != null) {
            if (!(type.equals(SExpressionConstants.BOOL_TYPE) || type
                    .equals(SExpressionConstants.CONTROL_TYPE)))
                throw new ParseError(expression,
                        "Found non-Boolean local variable where Bool sort was expected: "
                                + expression.toString());

            int partition = getPartitionBoolVariable(expression);
            return PropositionalVariable.create((Token) expression, partition);
        }

        if (isPropositionalVariable(expression)) {
            int partition = getPartitionBoolVariable(expression);
            return PropositionalVariable.create((Token) expression, partition);
        }

        if (isTseitinVariable(expression)) {
            PropositionalVariable var = PropositionalVariable
                    .create((Token) expression);

            if (!tseitinVariables.contains(var))
                tseitinVariables.add(var);
            return var;
        }

        if (isFormulaLetKey(expression)) {
            Formula value = letFormulaDefinitions.get(expression);
            assert (value != null);
            return value;
        }

        Token operator = isBooleanCombination(expression);

        if (operator != null) {
            if (operator.equals(SExpressionConstants.NOT)) {
                if (expression.getChildren().size() != 2)
                    throw new ParseError(expression,
                            "Expected exactly 1 expression after 'not'.");
                Formula negatedFormula = parseFormulaBody(expression
                        .getChildren().get(1));
                return NotFormula.create(negatedFormula);
            }

            if (operator.equals(SExpressionConstants.AND)) {
                if (expression.getChildren().size() < 2)
                    throw new ParseError(expression,
                            "Expected at least 1 expression after 'and'.");
                List<Formula> formulaList = new ArrayList<Formula>(expression
                        .getChildren().size() - 1);
                for (SExpression child : expression.getChildren().subList(1,
                        expression.getChildren().size())) {
                    formulaList.add(parseFormulaBody(child));
                }
                return AndFormula.generate(formulaList);
            }

            if (operator.equals(SExpressionConstants.OR)) {
                if (expression.getChildren().size() < 2)
                    throw new ParseError(expression,
                            "Expected at least 1 expression after 'or'.");
                List<Formula> formulaList = new ArrayList<Formula>(expression
                        .getChildren().size() - 1);
                for (SExpression child : expression.getChildren().subList(1,
                        expression.getChildren().size())) {
                    formulaList.add(parseFormulaBody(child));
                }
                return OrFormula.generate(formulaList);
            }

            if (operator.equals(SExpressionConstants.XOR)) {
                if (expression.getChildren().size() < 2)
                    throw new ParseError(expression,
                            "Expected at least 1 expression after 'xor'.");
                List<Formula> formulaList = new ArrayList<Formula>(expression
                        .getChildren().size() - 1);
                for (SExpression child : expression.getChildren().subList(1,
                        expression.getChildren().size())) {
                    formulaList.add(parseFormulaBody(child));
                }
                return XorFormula.generate(formulaList);
            }

            if (operator.equals(SExpressionConstants.IMPLIES)
                    || operator.equals(SExpressionConstants.IMPLIES_ALT)) {
                if (expression.getChildren().size() != 3)
                    throw new ParseError(expression,
                            "Expected 2 arguments for '=>'.");
                Formula leftSide = parseFormulaBody(expression.getChildren()
                        .get(1));
                Formula rightSide = parseFormulaBody(expression.getChildren()
                        .get(2));
                return ImpliesFormula.create(leftSide, rightSide);
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
                return PropositionalIte.create(condition, thenBranch,
                        elseBranch);
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

            List<Term> termList = new ArrayList<Term>(expression.getChildren()
                    .size() - 1);
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
                    indexGuard = PropositionalConstant.create(true);
                    valueConstraint = parseFormulaBody(property);
                } else if (!property.getChildren().get(0)
                        .equals(SExpressionConstants.IMPLIES)
                        && !property.getChildren().get(0)
                                .equals(SExpressionConstants.IMPLIES_ALT)) {
                    // also not an implication
                    indexGuard = PropositionalConstant.create(true);
                    valueConstraint = parseFormulaBody(property);
                } else { // we have an implication
                    if (property.getChildren().size() != 3)
                        throw new ParseError(property,
                                "Malformed array property!");
                    assert (property.getChildren().get(0)
                            .equals(SExpressionConstants.IMPLIES) || property
                            .getChildren().get(0)
                            .equals(SExpressionConstants.IMPLIES_ALT));

                    indexGuard = parseFormulaBody(property.getChildren().get(1));
                    valueConstraint = parseFormulaBody(property.getChildren()
                            .get(2));
                }

                try {
                    return ArrayProperty.create(currentUVars, indexGuard,
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

        UninterpretedFunction function = isUninterpredFunctionInstance(expression);
        if (function != null) {
            if (!(function.getType().equals(SExpressionConstants.BOOL_TYPE)))
                throw new ParseError(
                        expression,
                        "Non-Boolean uninterpreted function encountered, where sort Boolean was expected: "
                                + function.getName().toString());

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
                int partition = getPartitionUninterpretedFunction(function);
                return UninterpretedPredicateInstance.create(function,
                        parameters, partition);
            } catch (SuraqException exc) {
                throw new RuntimeException(
                        "Unexpected situation while parsing uninterpreted function instance.");
            }
        }

        FunctionMacro macro = isMacroInstance(expression);
        if (macro != null) {
            if (!macro.getType().equals(SExpressionConstants.BOOL_TYPE))
                throw new ParseError(expression,
                        "Bool macro expected. Received type: "
                                + macro.getType().toString());
            List<SExpression> paramExpressions = macro.getNumParams() == 0 ? new ArrayList<SExpression>()
                    : expression.getChildren().subList(1,
                            expression.getChildren().size());
            if (paramExpressions.size() != macro.getNumParams())
                throw new ParseError(expression, "Expected "
                        + macro.getNumParams() + "parameters for macro "
                        + macro.getName().toString() + ", got "
                        + paramExpressions.size() + " instead.");

            Map<Token, Term> paramMap = new HashMap<Token, Term>();
            assert (paramExpressions.size() == macro.getNumParams());
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
                return PropositionalFunctionMacroInstance.create(
                        (PropositionalFunctionMacro) macro, paramMap);
            } catch (InvalidParametersException exc) {
                throw new RuntimeException(
                        "Unexpected condition while creating function-macro instance.",
                        exc);
            }
        }

        // we have something we cannot handle
        if (expression instanceof Token)
            throw new ParseError(expression, "Undeclared identifier: "
                    + expression.toString());
        else {
            System.err
                    .println("We could not handle an Expression and it was no Token.");
            System.err.println("It was a:"
                    + expression.getClass().getName()
                    + " and its content was: "
                    + (expression.toString().length() >= 30 ? expression
                            .toString().substring(0, 30) + "..." : expression
                            .toString()));
            System.err.println("Full Exception coming soon...");
            throw new ParseError(expression, "Error parsing formula body.");
        }
    }

    /**
     * Determines the assert partition of a <code>PropositionalVariable</code>,
     * based on previous assert-partition information stored in
     * <code>boolVariables</code>.
     * 
     * @param expression
     *            the expression to check
     * @return the variables assert partition
     */
    private int getPartitionBoolVariable(SExpression expression) {

        for (PropositionalVariable var : boolVariables)
            if (var.equals(PropositionalVariable.create((Token) expression))) {
                Set<Integer> partitions = var.getPartitionsFromSymbols();
                return partitions.iterator().next();
            }

        return SMTLibParser.GLOBAL_PARTITION;
    }

    /**
     * Determines the assert partition of a <code>DomainVariable</code>, based
     * on previous assert-partition information stored in
     * <code>domainVariables</code>.
     * 
     * @param expression
     *            the expression to check
     * @return the variables assert partition
     */
    private int getPartitionDomainVariable(SExpression expression) {
        for (DomainVariable var : domainVariables)
            if (var.equals(DomainVariable.create((Token) expression))) {
                Set<Integer> partitions = var.getPartitionsFromSymbols();
                return partitions.iterator().next();
            }

        return SMTLibParser.GLOBAL_PARTITION;
    }

    /**
     * Determines the assert partition of a <code>ArrayVariable</code>, based on
     * previous assert-partition information stored in
     * <code>arrayVariables</code>.
     * 
     * @param expression
     *            the expression to check
     * @return the variables assert partition
     */
    private int getPartitionArrayVariable(SExpression expression) {
        for (ArrayVariable var : arrayVariables)
            if (var.equals(ArrayVariable.create((Token) expression))) {
                Set<Integer> partitions = var.getPartitionsFromSymbols();
                return partitions.iterator().next();
            }

        return SMTLibParser.GLOBAL_PARTITION;
    }

    /**
     * Determines the assert partition of an <code>UninterpretedFunction</code>,
     * based on previous assert-partition information stored in
     * <code>uninterpretedFunctions</code>.
     * 
     * @param function
     *            the function to check
     * @return the <code>function</code>'s assert partition
     */
    private int getPartitionUninterpretedFunction(UninterpretedFunction function) {
        for (UninterpretedFunction fun : functions)
            if (fun.equals(function)) {
                Set<Integer> partitions = fun.getAssertPartitionFromSymbols();
                return partitions.iterator().next();
            }

        return SMTLibParser.GLOBAL_PARTITION;
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
    protected Term parseTerm(SExpression expression) throws ParseError {

        if (isTermLetKey(expression)) {
            Term value = letTermDefinitions.get(expression);
            assert (value != null);
            return value;
        }

        if (expression.toString().charAt(0) == SMTLibParser.REF_TERM) {
            // resolve reference with LUT
            assert (expression instanceof Token);
            Token pureKey = Token.generate(expression.toString().substring(1));
            Term term = this.terms.get(pureKey);

            if (term == null)
                throw new ParseError(expression,
                        "could not find a matching term-LUT-entry!");

            return term;
        }

        if (isUVar(expression)) { // Takes precedence over other variable types
            int partition = getPartitionDomainVariable(expression);
            return DomainVariable.create((Token) expression, partition);
        }

        SExpression type = isLocalVariable(expression); // takes precedence over
                                                        // global variables.
        if (type != null) {
            if (type.equals(SExpressionConstants.ARRAY_TYPE)) {
                int partition = getPartitionArrayVariable(expression);
                return ArrayVariable.create((Token) expression, partition);
            }
            if (type.equals(SExpressionConstants.VALUE_TYPE)) {
                int partition = getPartitionDomainVariable(expression);
                return DomainVariable.create((Token) expression, partition);
            }
            if (type.equals(SExpressionConstants.BOOL_TYPE)
                    || type.equals(SExpressionConstants.CONTROL_TYPE)) {

                int partition = getPartitionBoolVariable(expression);
                return PropositionalVariable.create((Token) expression,
                        partition);
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
                return ArrayIte.create(condition, (ArrayTerm) thenBranch,
                        (ArrayTerm) elseBranch);

            if (thenBranch instanceof DomainTerm
                    && elseBranch instanceof DomainTerm)
                return DomainIte.create(condition, (DomainTerm) thenBranch,
                        (DomainTerm) elseBranch);

            if (thenBranch instanceof PropositionalTerm
                    && elseBranch instanceof PropositionalTerm)
                return FormulaTerm.create((PropositionalIte.create(condition,
                        (PropositionalTerm) thenBranch,
                        (PropositionalTerm) elseBranch)));

            throw new ParseError(expression,
                    "Incompatible types in 'ite' expression");
        }

        if (isArrayVariable(expression)) {
            int partition = getPartitionArrayVariable(expression);
            return ArrayVariable.create(expression.toString(), partition);
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

            return ArrayWrite.create((ArrayTerm) arrayTerm,
                    (DomainTerm) indexTerm, (DomainTerm) valueTerm);
        }

        if (isDomainVariable(expression)) {
            int partition = getPartitionDomainVariable(expression);
            return DomainVariable.create(expression.toString(), partition);
        }

        UninterpretedFunction function = isUninterpredFunctionInstance(expression);
        if (function != null) {
            // if (function.getType().equals(SExpressionConstants.BOOL_TYPE))
            // throw new ParseError(expression,
            // "Boolean uninterpreted function encountered, where Term was expected: "
            // + function.getName().toString());
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
                int partition = getPartitionUninterpretedFunction(function);
                if (function.getType().equals(SExpressionConstants.VALUE_TYPE))
                    return UninterpretedFunctionInstance.create(function,
                            parameters, partition);
                else {
                    assert (function.getType()
                            .equals(SExpressionConstants.BOOL_TYPE));
                    return UninterpretedPredicateInstance.create(function,
                            parameters, partition);
                }
            } catch (SuraqException exc) {
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

            return ArrayRead.create((ArrayTerm) arrayTerm,
                    (DomainTerm) indexTerm);
        }

        if (isPropositionalConstOrVar(expression)) {
            if (expression.equals(SExpressionConstants.TRUE))
                return PropositionalConstant.create(true);
            else if (expression.equals(SExpressionConstants.FALSE))
                return PropositionalConstant.create(false);

            int partition = getPartitionBoolVariable(expression);
            PropositionalVariable variable = PropositionalVariable.create(
                    (Token) expression, partition);
            if (!boolVariables.contains(variable)
                    && !controlVariables.contains(variable))
                throw new RuntimeException(
                        "Unexpected situation while handling variable "
                                + variable.toString());
            return variable;
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
            assert (paramExpressions.size() == macro.getNumParams());
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
                if (macro.getType().equals(SExpressionConstants.BOOL_TYPE)) {
                    assert (macro instanceof PropositionalFunctionMacro);
                    return FormulaTerm
                            .create(PropositionalFunctionMacroInstance.create(
                                    (PropositionalFunctionMacro) macro,
                                    paramMap));
                } else {
                    assert (macro instanceof TermFunctionMacro);
                    return TermFunctionMacroInstance.create(
                            (TermFunctionMacro) macro, paramMap);
                }
            } catch (InvalidParametersException exc) {
                throw new RuntimeException(
                        "Unexpected condition while creating function-macro instance.",
                        exc);
            }
        }

        // as a last resort, try interpreting the expression as a formula
        // this will throw a parse error, if it fails.
        Formula formula = parseFormulaBody(expression);
        return FormulaTerm.create(formula);
    }

    /**
     * Parses the list of universally quantified variables.
     * 
     * @param uVarsExpression
     *            the first argument of a <code>forall</code> expression
     * @return the collection of universally quantified variables.
     */
    protected Collection<DomainVariable> parseUVars(SExpression uVarsExpression)
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

            int partition = getPartitionDomainVariable(child.getChildren().get(
                    0));
            if (!uVars.add(DomainVariable.create((Token) child.getChildren()
                    .get(0), partition))) {
                throw new ParseError(child.getChildren().get(0),
                        "Duplicate variable in quantifier scope: "
                                + child.getChildren().get(0).toString());
            }
        }
        return uVars;
    }

    /**
     * Checks if the given expression is an if-then-else term
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the first child of <code>expression</code>
     *         is a <code>Token</code> and it equals the ITE operator.
     */
    protected boolean isIteTerm(SExpression expression) {
        if (expression instanceof Token)
            return false;
        if (expression.getChildren().size() < 1)
            return false;
        if (expression.getChildren().get(0).equals(SExpressionConstants.ITE))
            return true;

        return false;
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
    protected FunctionMacro isMacroInstance(SExpression expression) {
        if (expression instanceof Token) {
            // Could be a macro without parameters
            return macros.get(expression);
        } else {
            // Could be a macro with parameters
            if (expression.getChildren().size() < 2)
                return null;
            if (!(expression.getChildren().get(0) instanceof Token))
                return null;

            assert (expression.getChildren().get(0) instanceof Token);
            Token macroName = (Token) expression.getChildren().get(0);
            return macros.get(macroName);
        }
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
    protected boolean isArrayProperty(SExpression expression) {
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
     * Checks whether the given expression is an array read.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the first child of <code>expression</code>
     *         is the <code>select</code> token, <code>false</code> otherwise.
     */
    protected boolean isArrayRead(SExpression expression) {
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
    protected boolean isArrayWrite(SExpression expression) {
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
     * Checks whether the given expression is an equality instance.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the given expression is an equality
     *         expression, <code>false</code> otherwise.
     */
    protected boolean isEquality(SExpression expression) {
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
    protected Token isBooleanCombination(SExpression expression) {
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
                || operator.equals(SExpressionConstants.IMPLIES_ALT)
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
    protected boolean isPropositionalVariable(SExpression expression) {
        if (!(expression instanceof Token))
            return false;
        Token token = (Token) expression;
        PropositionalVariable variable = PropositionalVariable.create(token);
        if (boolVariables.contains(variable)
                || controlVariables.contains(variable))
            return true;
        else
            return false;
    }

    /**
     * Checks if the given expression is a Tseitin variable.
     * 
     * @param expression
     *            the expression to check
     * @return <code>true</code> if the given expression is a Tseitin variable,
     *         <code>false</code> otherwise.
     */
    protected boolean isTseitinVariable(SExpression expression) {

        if (!(expression instanceof Token))
            return false;

        Token token = (Token) expression;
        PropositionalVariable variable = PropositionalVariable.create(token);

        if (expression.toString().startsWith("k!")) {
            if (boolVariables.contains(variable)
                    || controlVariables.contains(variable))
                assert (false);
            // System.out.println("INFO: Identified Tseitin variable: " +
            // token);
            return true;
        }

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
    protected boolean isPropositionalConstant(SExpression expression) {
        return (expression.equals(SExpressionConstants.TRUE) || expression
                .equals(SExpressionConstants.FALSE));
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
    protected SExpression isLocalVariable(SExpression expression) {
        if (currentLocals == null)
            return null;

        return currentLocals.get(expression);
    }

    /**
     * Checks if the given expression is a propositional variable or constant.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the given expression is a propositional
     *         variable or constant, <code>false</code> otherwise.
     */
    protected boolean isPropositionalConstOrVar(SExpression expression) {
        if (!(expression instanceof Token))
            return false;

        if (expression.equals(SExpressionConstants.TRUE))
            return true;

        if (expression.equals(SExpressionConstants.FALSE))
            return true;

        PropositionalVariable variable = PropositionalVariable
                .create((Token) expression);
        if (boolVariables.contains(variable))
            // || controlVariables.contains(variable))
            return true;
        else
            return false;
    }

    /**
     * Checks whether the given expression is a domain variable
     * 
     * @param expression
     *            the expression to check
     * @return <code>true</code> if the given expression is a domain variable,
     *         <code>false</code> otherwise.
     */
    protected boolean isDomainVariable(SExpression expression) {
        if (!(expression instanceof Token))
            return false;
        return domainVariables.contains(DomainVariable
                .create((Token) expression));
    }

    /**
     * Checks whether the given expression is an array variable
     * 
     * @param expression
     *            the expression to check
     * @return <code>true</code> if the given expression is an array variable,
     *         <code>false</code> otherwise.
     */
    protected boolean isArrayVariable(SExpression expression) {
        if (!(expression instanceof Token))
            return false;
        return arrayVariables
                .contains(ArrayVariable.create((Token) expression));
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
    protected UninterpretedFunction isUninterpredFunctionInstance(
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
     * Checks if the given expression is a universally quantified variable (in
     * current scope).
     * 
     * @param expression
     *            the expression to check
     * @return <code>true</code> if the expression is a universally quantified
     *         variable, <code>false</code> otherwise.
     */
    protected boolean isUVar(SExpression expression) {
        if (currentUVars == null)
            return false;

        if (!(expression instanceof Token))
            return false;

        return (this.currentUVars.contains(DomainVariable
                .create((Token) expression)));
    }

    /**
     * Checks whether the given expression is an let instance.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the given expression is an let expression,
     *         <code>false</code> otherwise.
     */
    protected boolean isLet(SExpression expression) {
        if (expression instanceof Token)
            return false;
        if (expression.getChildren().size() != 3)
            return false;
        if (!(expression.getChildren().get(0) instanceof Token)) // let
            return false;
        assert (expression.getChildren().get(0) instanceof Token);
        if (!(expression.getChildren().get(0).equals(SExpressionConstants.LET)))
            return false;

        for (SExpression child : expression.getChildren().get(1).getChildren()) {
            if (child.size() != 2)
                return false;
            if (!(child.getChildren().get(0) instanceof Token))
                return false;
        }

        return true;
    }

    /**
     * Checks whether the given expression is a key defined by a let expression.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the given expression is a key defined by a
     *         let expression, <code>false</code> otherwise.
     */
    protected boolean isFormulaLetKey(SExpression expression) {
        if (!(expression instanceof Token))
            return false;
        return letFormulaDefinitions.containsKey(expression);
    }

    /**
     * Checks whether the given expression is a key defined by a let expression.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the given expression is a key defined by a
     *         let expression, <code>false</code> otherwise.
     */
    protected boolean isTermLetKey(SExpression expression) {
        if (!(expression instanceof Token))
            return false;
        return letTermDefinitions.containsKey(expression);
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
     * Returns a copy of the list of Tseitin variables.
     * 
     * @return a copy of the <code>boolVariables</code>
     */
    public List<PropositionalVariable> getTseitinVariables() {
        return new ArrayList<PropositionalVariable>(tseitinVariables);
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
     * Returns a copy of the list of variables on which control logic may
     * <em>not</em> depend.
     * 
     * @return a copy of the list of variables on which control logic may
     *         <em>not</em> depend.
     */
    public List<Token> getNoDependenceVariables() {
        return new ArrayList<Token>(noDependenceVariables);
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

    /**
     * Handles a let expression that defines Tseitin variables.
     * 
     * @param expr
     * @return
     * @throws ParseError
     */
    protected final Formula handleLet(SExpression expr) throws ParseError {
        assert (expr.size() == 3);
        assert (expr.getChildren().get(0) instanceof Token);
        assert (expr.getChildren().get(0).equals(SExpressionConstants.LET));

        Set<Token> currentLetTokens = new HashSet<Token>();
        for (SExpression defineExpr : expr.getChildren().get(1).getChildren()) {
            assert (defineExpr.size() == 2);
            assert (defineExpr.getChildren().get(0) instanceof Token);
            Token key = (Token) defineExpr.getChildren().get(0);

            if (isTerm(defineExpr.getChildren().get(1))) {
                Term value = parseTerm(defineExpr.getChildren().get(1));
                letTermDefinitions.put(key, value);
            } else {
                Formula value = parseFormulaBody(defineExpr.getChildren()
                        .get(1));
                letFormulaDefinitions.put(key, value);
            }
            currentLetTokens.add(key);
        }

        // String formulaString = expr.getChildren().get(2).toString();
        //
        // for (Token token : letFormulaDefinitions.keySet())
        // formulaString = formulaString.replaceAll(token.toString()
        // + "[\\t\\n\\x0B\\f\\r(]", letFormulaDefinitions.get(token)
        // .toString());
        //
        // SExpression tmpExpr = SExpression.fromString(formulaString);

        // SExpression tmpExpr = expr.getChildren().get(2);
        // tmpExpr.replace(letFormulaDefinitions);

        Formula result = parseFormulaBody(expr.getChildren().get(2));

        for (Token key : currentLetTokens) {
            letFormulaDefinitions.remove(key);
            letTermDefinitions.remove(key);
        }

        return result;
    }

    /**
     * 
     * @param expression
     * @return <code>true</code> iff the given expression is a term and not a
     *         formula.
     */
    protected boolean isTerm(SExpression expression) {
        if (isDomainVariable(expression))
            return true;

        UninterpretedFunction function = isUninterpredFunctionInstance(expression);
        if (function != null) {
            if (function.getType().equals(SExpressionConstants.VALUE_TYPE))
                return true;
        }

        if (isArrayRead(expression))
            return true;

        if (isArrayWrite(expression))
            return true;

        if (isArrayVariable(expression))
            return true;

        return false;
    }
}
