/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.parser;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;

/**
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */

public class TseitinParser extends SMTLibParser {

    /**
     * The formula that results from parsing.
     */
    private Formula rootFormula = null;

    /**
     * 
     * Constructs a new <code>TseitinParser</code>.
     * 
     * @param root
     *            the root expression to parse.
     * @param domainVars
     *            proof domain variables
     * @param propsitionalVars
     *            proof propositional variables
     * @param arrayVars
     *            proof array variables
     * @param uninterpretedFunctions
     *            proof uninterpreted Functions
     */
    public TseitinParser(SExpression root, Set<DomainVariable> domainVars,
            Set<PropositionalVariable> propsitionalVars,
            Set<ArrayVariable> arrayVars,
            Set<UninterpretedFunction> uninterpretedFunctions) {

        this.boolVariables = propsitionalVars;
        this.arrayVariables = arrayVars;
        this.domainVariables = domainVars;
        this.functions = uninterpretedFunctions;
        this.rootExpr = root;
    }

    /**
     * Parses the root s-expression into a formula, which can then be retrieved
     * using <code>getFormula</code>.
     * 
     * @see at.iaik.suraq.parser.Parser#parse()
     */
    @Override
    public void parse() throws ParseError {

        // Example:
        //
        // (goals
        // (goal
        // (or d k!0)
        // (or a k!0)
        // (or (not d) (not a) (not k!0))
        // (or a k!1)
        // (or (not c) k!1)
        // (or (not a) c (not k!1))
        // (or k!1 k!2)
        // (or b k!2)
        // (or (not e) k!2)
        // (or a k!2)
        // (or c k!2)
        // (or k!0 k!2)
        // (or (not k!1) (not b) e (not a) (not c) (not k!0) (not k!2))
        // (or (not k!2) a b)
        // :precision precise :depth 3
        // )
        // )
        // sat

        assert (rootExpr.getChildren().size() == 1);

        SExpression goalExpr = rootExpr.getChildren().get(0).getChildren()
                .get(1);

        assert (goalExpr.getChildren().get(0).equals(SExpressionConstants.GOAL));
        goalExpr.getChildren().remove(0);

        int numChildren = goalExpr.size();

        assert (goalExpr.getChildren().get(numChildren - 4).equals(new Token(
                ":precision")));
        assert (goalExpr.getChildren().get(numChildren - 3).equals(new Token(
                "precise")));
        assert (goalExpr.getChildren().get(numChildren - 2).equals(new Token(
                ":depth")));

        goalExpr.removeChild(numChildren - 1);
        goalExpr.removeChild(numChildren - 2);
        goalExpr.removeChild(numChildren - 3);
        goalExpr.removeChild(numChildren - 4);

        List<Formula> clauses = new ArrayList<Formula>();
        for (SExpression expr : goalExpr.getChildren()) {
            if (isLet(expr))
                clauses.add(handleLet(expr));
            else
                clauses.add(parseFormulaBody(expr));
        }
        rootFormula = new AndFormula(clauses);
        parsingSuccessfull = true;

    }

    /**
     * Handles a let expression that defines Tseitin variables.
     * 
     * @param expr
     * @return
     * @throws ParseError
     */
    private Formula handleLet(SExpression expr) throws ParseError {
        assert (expr.size() == 3);
        assert (expr.getChildren().get(0) instanceof Token);
        assert (expr.getChildren().get(0).equals(SExpressionConstants.LET));

        Map<Token, SExpression> letDefinitions = new HashMap<Token, SExpression>();

        for (SExpression defineExpr : expr.getChildren().get(1).getChildren()) {
            assert (defineExpr.size() == 2);
            assert (defineExpr.getChildren().get(0) instanceof Token);
            Token key = (Token) defineExpr.getChildren().get(0);
            SExpression value = defineExpr.getChildren().get(1);

            letDefinitions.put(key, value);
        }

        String formulaString = expr.getChildren().get(2).toString();

        for (Token token : letDefinitions.keySet())
            formulaString = formulaString.replaceAll(token.toString(),
                    letDefinitions.get(token).toString());

        return parseFormulaBody(SExpression.fromString(formulaString));

    }

    /**
     * Returns the root formula that resulted from parsing, or <code>null</code>
     * if parsing was not successful.
     * 
     * @return the formula that resulted from parsing, or <code>null</code> if
     *         parsing was not successful.
     */
    public Formula getRootFormula() {
        if (!wasParsingSuccessfull())
            return null;
        return rootFormula;
    }

    /**
     * Calculates the corresponding formula for each tseitin variable.
     * 
     * @return the map of tseitin variables with corresponding formula.
     */
    public Map<PropositionalVariable, Formula> getTseitinEncoding() {

        Map<PropositionalVariable, Formula> tseitinEncoding = new HashMap<PropositionalVariable, Formula>();

        assert (rootFormula instanceof AndFormula);
        List<Formula> clauses = ((AndFormula) rootFormula).getConjuncts();

        try {
            FileWriter fstream = new FileWriter("clauses.smt2");
            BufferedWriter buffer = new BufferedWriter(fstream);
            for (Formula clause : clauses) {
                buffer.write(clause.toString().replaceAll("\\s{2,}", " ")
                        .replace("\n", ""));
                buffer.newLine();
            }
            buffer.flush();
            buffer.close();
            fstream.close();
        } catch (IOException exc) {
            System.err.println("Error while writing to file clauses.smt2. ");
            exc.printStackTrace();
        }

        int currTseitinIndex = 0;
        List<Formula> currClauses = new ArrayList<Formula>();
        boolean finishCurrTseitinDef = false;
        TseitinVariableState tseitinState = null;

        for (int i = 0; i < clauses.size(); i++) {
            Formula clause = clauses.get(i);
            if (clause instanceof OrFormula) {
                List<Integer> tseitinIndices = getTseitinVariablesFromFormula(clause);
                int numTseitinVars = tseitinIndices.size();
                if (numTseitinVars > 0) {
                    // check if current tseitin variable is in clause
                    if (tseitinIndices.contains(currTseitinIndex)) {
                        // check if clause doesn`t contain any larger idx
                        Collections.sort(tseitinIndices);
                        if (tseitinIndices.get(numTseitinVars - 1) <= currTseitinIndex) {
                            // if clause is first clause of tseitin var def
                            if (currClauses.size() == 0) {
                                tseitinState = setTseitinVariableState(clause,
                                        this.tseitinVariables
                                                .get(currTseitinIndex));
                                currClauses.add(clause);
                            } else if (checkAndUpdateTseitinVariableState(
                                    clause, tseitinState,
                                    this.tseitinVariables.get(currTseitinIndex))) {
                                currClauses.add(clause);
                            } else
                                finishCurrTseitinDef = true;
                        } else
                            finishCurrTseitinDef = true;
                    } else
                        finishCurrTseitinDef = true;
                } else
                    finishCurrTseitinDef = true;
            } else
                finishCurrTseitinDef = true;

            if (finishCurrTseitinDef == true) {
                finishCurrTseitinDef = false;
                if (currClauses.size() > 0) {
                    PropositionalVariable currTseitinVar = this.tseitinVariables
                            .get(currTseitinIndex);
                    Formula posFormula = buildPositiveFormula(currClauses,
                            currTseitinVar);
                    Formula negFormula = buildNegativeFormula(currClauses,
                            currTseitinVar);
                    assert (posFormula != null);
                    assert (negFormula != null);

                    checkEquivalenceOfFormulas(posFormula, negFormula);

                    // calc partitions of tseitin variable
                    Set<Integer> partitions = posFormula
                            .getPartitionsFromSymbols();

                    int partition;
                    if (partitions.size() == 2) {
                        assert (partitions.remove(-1));
                        partition = partitions.iterator().next();
                    } else {
                        assert (partitions.size() == 1);
                        partition = partitions.iterator().next();
                    }
                    assert (partition != 0);

                    tseitinEncoding
                            .put(new PropositionalVariable(currTseitinVar
                                    .getVarName(), partition), posFormula);

                    System.out.println("INFO: Encoded Tseitin variable "
                            + currTseitinVar.getVarName());

                    // Compute something of clauses
                    currTseitinIndex++;
                    currClauses = new ArrayList<Formula>();
                    i--; // re-check clause
                }
            }
        }

        return tseitinEncoding;
    }

    /**
     * Checks if the given formulas imply each other.
     * 
     * @param formula1
     *            the first formula
     * 
     * @param formula2
     *            the second formula
     * 
     * @return returns true, if the two variables imply each other.
     */
    private boolean checkEquivalenceOfFormulas(Formula formula1,
            Formula formula2) {
        return true;
    }

    /**
     * Builds the formula, which is implied by the current tseitin variable.
     * 
     * @param clauses
     *            clauses from which the formula is constructed
     * 
     * @param currTseitinVar
     *            current tseitin variable.
     * 
     * @return formula, which is implied by the current tseitin variable.
     */
    private Formula buildNegativeFormula(List<Formula> clauses,
            PropositionalVariable currTseitinVar) {

        List<Formula> conjuncts = new ArrayList<Formula>();

        Boolean first = null;
        Boolean neg = null;

        for (Formula clause : clauses) {
            boolean processed = false;
            assert (clause instanceof OrFormula);
            List<Formula> literals = ((OrFormula) clause).getDisjuncts();
            int numLiterals = literals.size();
            Formula firstLiteral = literals.get(0);
            Formula lastLiteral = literals.get(numLiterals - 1);

            if (firstLiteral instanceof PropositionalVariable) {
                if (firstLiteral.equals(currTseitinVar)) {
                    first = true;
                    neg = false;
                    processed = true;
                }
            }
            if (firstLiteral instanceof NotFormula && processed == false) {
                firstLiteral = ((NotFormula) firstLiteral).getNegatedFormula();
                if (firstLiteral instanceof PropositionalVariable) {
                    if (firstLiteral.equals(currTseitinVar)) {
                        first = true;
                        neg = true;
                        processed = true;
                    }
                }
            }
            if (lastLiteral instanceof PropositionalVariable
                    && processed == false) {
                if (lastLiteral.equals(currTseitinVar)) {
                    first = false;
                    neg = false;
                    processed = true;
                }
            }
            if (lastLiteral instanceof NotFormula && processed == false) {
                lastLiteral = ((NotFormula) lastLiteral).getNegatedFormula();
                if (lastLiteral instanceof PropositionalVariable) {
                    if (lastLiteral.equals(currTseitinVar)) {
                        first = false;
                        neg = true;
                        processed = true;
                    }
                }
            }
            if (!processed)
                throw new RuntimeException(
                        "In the definition of a tseitin variable, the variable should occurr in the beginning or in the end of the clause");

            if (!neg)
                continue;

            if (first)
                literals.remove(0);

            else
                literals.remove(numLiterals - 1);

            conjuncts.add(new OrFormula(literals));

        }
        return new AndFormula(conjuncts);
    }

    /**
     * Builds the formula, which implies current tseitin variable.
     * 
     * @param clauses
     *            clauses from which the formula is constructed
     * 
     * @param currTseitinVar
     *            current tseitin variable.
     * 
     * @return formula, which implies current tseitin variable
     */
    private Formula buildPositiveFormula(List<Formula> clauses,
            PropositionalVariable currTseitinVar) {

        List<Formula> disjuncts = new ArrayList<Formula>();

        Boolean first = null;
        Boolean neg = null;

        for (Formula clause : clauses) {
            boolean processed = false;

            assert (clause instanceof OrFormula);
            List<Formula> literals = ((OrFormula) clause).getDisjuncts();
            int numLiterals = literals.size();
            Formula firstLiteral = literals.get(0);
            Formula lastLiteral = literals.get(numLiterals - 1);

            if (firstLiteral instanceof PropositionalVariable) {
                if (firstLiteral.equals(currTseitinVar)) {
                    first = true;
                    neg = false;
                    processed = true;
                }
            }
            if (firstLiteral instanceof NotFormula && processed == false) {
                firstLiteral = ((NotFormula) firstLiteral).getNegatedFormula();
                if (firstLiteral instanceof PropositionalVariable) {
                    if (firstLiteral.equals(currTseitinVar)) {
                        first = true;
                        neg = true;
                        processed = true;
                    }
                }
            }
            if (lastLiteral instanceof PropositionalVariable
                    && processed == false) {
                if (lastLiteral.equals(currTseitinVar)) {
                    first = false;
                    neg = false;
                    processed = true;
                }
            }
            if (lastLiteral instanceof NotFormula && processed == false) {
                lastLiteral = ((NotFormula) lastLiteral).getNegatedFormula();
                if (lastLiteral instanceof PropositionalVariable) {
                    if (lastLiteral.equals(currTseitinVar)) {
                        first = false;
                        neg = true;
                        processed = true;
                    }
                }
            }
            if (!processed)
                throw new RuntimeException(
                        "In the definition of a tseitin variable, the variable should occurr in the beginning or in the end of the clause");

            if (neg)
                continue;

            if (first)
                literals.remove(0);

            else
                literals.remove(numLiterals - 1);

            disjuncts.add(new NotFormula(new OrFormula(literals)));

        }
        return new OrFormula(disjuncts);
    }

    /**
     * Checks if the occurrence of the tseitin variable in the clause is allowed
     * according the attributes in the <code>TseitinVariableState</code> and
     * updates the attributes.
     * 
     * @param clause
     *            clause to analyze
     * @param tseitinState
     *            attributes of the tseitin variables
     * @param currTseitinVar
     *            current tseitin variable.
     * 
     * @return <code>TseitinVariableState</code> with attributes set
     */
    private boolean checkAndUpdateTseitinVariableState(Formula clause,
            TseitinVariableState tseitinState,
            PropositionalVariable currTseitinVar) {

        assert (clause instanceof OrFormula);
        List<Formula> literals = ((OrFormula) clause).getDisjuncts();
        int numLiterals = literals.size();
        Formula firstLiteral = literals.get(0);
        Formula lastLiteral = literals.get(numLiterals - 1);

        if (firstLiteral instanceof PropositionalVariable) {
            if (firstLiteral.equals(currTseitinVar)) {
                if (!tseitinState.isFrontOccurrence())
                    return false;
                if (!tseitinState.isSign())
                    if (!tseitinState.isSignedChange()) {
                        tseitinState.setSignedChange(true);
                        tseitinState.setSign(true);
                    } else
                        return false;
            }
        }
        if (firstLiteral instanceof NotFormula) {
            firstLiteral = ((NotFormula) firstLiteral).getNegatedFormula();
            if (firstLiteral instanceof PropositionalVariable) {
                if (firstLiteral.equals(currTseitinVar)) {
                    if (!tseitinState.isFrontOccurrence())
                        return false;
                    if (tseitinState.isSign())
                        if (!tseitinState.isSignedChange()) {
                            tseitinState.setSignedChange(true);
                            tseitinState.setSign(false);
                        } else
                            return false;
                }
            }
        }
        if (lastLiteral instanceof PropositionalVariable) {
            if (lastLiteral.equals(currTseitinVar)) {
                if (tseitinState.isFrontOccurrence())
                    return false;
                if (!tseitinState.isSign())
                    if (!tseitinState.isSignedChange()) {
                        tseitinState.setSignedChange(true);
                        tseitinState.setSign(true);
                    } else
                        return false;
            }
        }
        if (lastLiteral instanceof NotFormula) {
            lastLiteral = ((NotFormula) lastLiteral).getNegatedFormula();
            if (lastLiteral instanceof PropositionalVariable) {
                if (lastLiteral.equals(currTseitinVar)) {
                    if (tseitinState.isFrontOccurrence())
                        return false;
                    if (tseitinState.isSign())
                        if (!tseitinState.isSignedChange()) {
                            tseitinState.setSignedChange(true);
                            tseitinState.setSign(false);
                        } else
                            return false;
                }
            }
        }

        return true;
    }

    /**
     * Creates a new <code>TseitinVariableState</code> and sets attributes
     * according to clause.
     * 
     * @param clause
     *            clause to analyze
     * 
     * @param currTseitinVar
     *            current tseitin variable.
     * 
     * @return <code>TseitinVariableState</code> with attributes set
     */
    private TseitinVariableState setTseitinVariableState(Formula clause,
            PropositionalVariable currTseitinVar) {

        Boolean frontOccurrence = null;
        boolean signChange = false;
        Boolean sign = null;
        boolean processed = false;

        assert (clause instanceof OrFormula);
        List<Formula> literals = ((OrFormula) clause).getDisjuncts();
        int numLiterals = literals.size();
        Formula firstLiteral = literals.get(0);
        Formula lastLiteral = literals.get(numLiterals - 1);

        if (firstLiteral instanceof PropositionalVariable) {
            if (firstLiteral.equals(currTseitinVar)) {
                frontOccurrence = true;
                sign = true;
                processed = true;
            }
        }
        if (firstLiteral instanceof NotFormula && processed == false) {
            firstLiteral = ((NotFormula) firstLiteral).getNegatedFormula();
            if (firstLiteral instanceof PropositionalVariable) {
                if (firstLiteral.equals(currTseitinVar)) {
                    frontOccurrence = true;
                    sign = false;
                    processed = true;
                }
            }
        }
        if (lastLiteral instanceof PropositionalVariable && processed == false) {
            if (lastLiteral.equals(currTseitinVar)) {
                assert (frontOccurrence == null);
                frontOccurrence = false;
                sign = true;
                processed = true;
            }
        }
        if (lastLiteral instanceof NotFormula && processed == false) {
            lastLiteral = ((NotFormula) lastLiteral).getNegatedFormula();
            if (lastLiteral instanceof PropositionalVariable) {
                if (lastLiteral.equals(currTseitinVar)) {
                    assert (frontOccurrence == null);
                    frontOccurrence = false;
                    sign = false;
                    processed = true;
                }
            }
        }
        if (!processed)
            throw new RuntimeException(
                    "In the definition of a tseitin variable, the variable should occurr in the beginning or in the end of the clause");

        return new TseitinVariableState(frontOccurrence, signChange, sign);
    }

    /**
     * Returns the indices of the found tseitin variables contained by the
     * formula.
     * 
     * @param formula
     *            formula, to extract variable indices from
     * 
     * @return indices of found tseitin variables
     */
    private List<Integer> getTseitinVariablesFromFormula(Formula formula) {

        List<Integer> tseitinIndices = new ArrayList<Integer>();

        Set<PropositionalVariable> propVars = formula
                .getPropositionalVariables();

        Iterator<PropositionalVariable> iterator = propVars.iterator();
        while (iterator.hasNext()) {
            PropositionalVariable propVar = iterator.next();
            int idx = tseitinVariables.indexOf(propVar);
            if (idx >= 0)
                tseitinIndices.add(idx);
        }
        return tseitinIndices;
    }
}
