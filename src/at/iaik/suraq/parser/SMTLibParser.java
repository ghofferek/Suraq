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
import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.exceptions.SuraqException;
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
import at.iaik.suraq.formula.FormulaTerm;
import at.iaik.suraq.formula.FunctionMacro;
import at.iaik.suraq.formula.ImpliesFormula;
import at.iaik.suraq.formula.NotFormula;
import at.iaik.suraq.formula.OrFormula;
import at.iaik.suraq.formula.ProofFormula;
import at.iaik.suraq.formula.PropositionalConstant;
import at.iaik.suraq.formula.PropositionalFunctionMacro;
import at.iaik.suraq.formula.PropositionalFunctionMacroInstance;
import at.iaik.suraq.formula.PropositionalIte;
import at.iaik.suraq.formula.PropositionalTerm;
import at.iaik.suraq.formula.PropositionalVariable;
import at.iaik.suraq.formula.Term;
import at.iaik.suraq.formula.TermFunctionMacro;
import at.iaik.suraq.formula.TermFunctionMacroInstance;
import at.iaik.suraq.formula.UninterpretedFunction;
import at.iaik.suraq.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.formula.XorFormula;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

public abstract class SMTLibParser extends Parser {

	/**
     * maps containing proof references
     */
	protected final Map<Token, ProofFormula> proofs = new HashMap<Token, ProofFormula>();
	
	protected final Map<Token, Formula> formulas = new HashMap<Token, Formula>();
	
	protected final Map<Token, Term> terms = new HashMap<Token, Term>();
	
    /**
     * constants for let expression types
     */
    public static final char REF_PROOF ='@';   
    public static final char REF_FORMULA = '$';     
    public static final char REF_TERM = '?';
    
    /**
     * The formula that results from parsing.
     */
    protected Formula mainFormula = null;

    /**
     * The list of control variables found during parsing
     */
    protected Set<PropositionalVariable> controlVariables = new HashSet<PropositionalVariable>();

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
    protected SExpression rootExpr=null;

    /**
     * A map of current local variables while parsing a function macro.
     */
    protected Map<Token, SExpression> currentLocals = null;

    /**
     * The set of universally quantified variables in current scope.
     */
    protected Collection<DomainVariable> currentUVars = null;
    	
	
	@Override
	public void parse() throws ParseError {
		// TODO Auto-generated method stub
		
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
    protected Formula parseFormulaBody(SExpression expression) throws ParseError {
    	
    	if (expression.toString().charAt(0)== REF_FORMULA) {
    		//resolve reference with LUT
    		assert(expression instanceof Token);
    		Token pureKey = new Token (expression.toString().substring(1));
    		Formula formula = this.formulas.get(pureKey);
    		
    		if (formula==null)
    			throw new ParseError(expression,
    					"could not find a matching formula-LUT-entry!");
    		
    		return formula;
    	}
    	
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

        SExpression type = isLocalVariable(expression); // takes precedence over
                                                        // global variables.
        if (type != null) {
            if (!(type.equals(SExpressionConstants.BOOL_TYPE) || type
                    .equals(SExpressionConstants.CONTROL_TYPE)))
                throw new ParseError(expression,
                        "Found non-Boolean local variable where Bool sort was expected: "
                                + expression.toString());
            return new PropositionalVariable((Token) expression);
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
                if (expression.getChildren().size() < 2)
                    throw new ParseError(expression,
                            "Expected at least 1 expression after 'and'.");
                List<Formula> formulaList = new ArrayList<Formula>();
                for (SExpression child : expression.getChildren().subList(1,
                        expression.getChildren().size())) {
                    formulaList.add(parseFormulaBody(child));
                }
                return new AndFormula(formulaList);
            }

            if (operator.equals(SExpressionConstants.OR)) {
                if (expression.getChildren().size() < 2)
                    throw new ParseError(expression,
                            "Expected at least 1 expression after 'or'.");
                List<Formula> formulaList = new ArrayList<Formula>();
                for (SExpression child : expression.getChildren().subList(1,
                        expression.getChildren().size())) {
                    formulaList.add(parseFormulaBody(child));
                }
                return new OrFormula(formulaList);
            }

            if (operator.equals(SExpressionConstants.XOR)) {
                if (expression.getChildren().size() < 2)
                    throw new ParseError(expression,
                            "Expected at least 1 expression after 'xor'.");
                List<Formula> formulaList = new ArrayList<Formula>();
                for (SExpression child : expression.getChildren().subList(1,
                        expression.getChildren().size())) {
                    formulaList.add(parseFormulaBody(child));
                }
                return new XorFormula(formulaList);
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
                } else if (!property.getChildren().get(0).equals(SExpressionConstants.IMPLIES)
                		&& !property.getChildren().get(0).equals(SExpressionConstants.IMPLIES_ALT)) {
                    // also not an implication
                    indexGuard = new PropositionalConstant(true);
                    valueConstraint = parseFormulaBody(property);
                } else { // we have an implication
                    if (property.getChildren().size() != 3)
                        throw new ParseError(property,
                                "Malformed array property!");
                    assert (property.getChildren().get(0).equals(SExpressionConstants.IMPLIES)
                    		|| property.getChildren().get(0).equals(SExpressionConstants.IMPLIES_ALT));
              
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
                return new UninterpretedPredicateInstance(function, parameters);
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
                return new PropositionalFunctionMacroInstance(
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
        else
            throw new ParseError(expression, "Error parsing formula body.");
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

    	if (expression.toString().charAt(0)== REF_TERM) {
    		//resolve reference with LUT
    		assert(expression instanceof Token);
    		Token pureKey = new Token (expression.toString().substring(1));
    		Term term = this.terms.get(pureKey);
    		
    		if (term==null)
    			throw new ParseError(expression,
    					"could not find a matching term-LUT-entry!");
    		
    		return term;
    	}    	
    	
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

            if (thenBranch instanceof PropositionalTerm
                    && elseBranch instanceof PropositionalTerm)
                return new FormulaTerm(new PropositionalIte(condition,
                        (PropositionalTerm) thenBranch,
                        (PropositionalTerm) elseBranch));

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
            if (function.getType().equals(SExpressionConstants.BOOL_TYPE))
                throw new ParseError(expression,
                        "Boolean uninterpreted function encountered, where Term was expected: "
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
                return new UninterpretedFunctionInstance(function, parameters);
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

            return new ArrayRead((ArrayTerm) arrayTerm, (DomainTerm) indexTerm);
        }

        if (isPropositionalConstOrVar(expression)) {
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
                    return new FormulaTerm(
                            new PropositionalFunctionMacroInstance(
                                    (PropositionalFunctionMacro) macro,
                                    paramMap));
                } else {
                    assert (macro instanceof TermFunctionMacro);
                    return new TermFunctionMacroInstance(
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
        return new FormulaTerm(formula);
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
        PropositionalVariable variable = new PropositionalVariable(token);
        if (boolVariables.contains(variable)
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

        PropositionalVariable variable = new PropositionalVariable(
                (Token) expression);
        if (boolVariables.contains(variable))
                //|| controlVariables.contains(variable))
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
    protected boolean isArrayVariable(SExpression expression) {
        if (!(expression instanceof Token))
            return false;
        return arrayVariables.contains(new ArrayVariable((Token) expression));
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

        return (this.currentUVars.contains(new DomainVariable(
                (Token) expression)));
    }    
}