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
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.main.SuraqOptions;
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
import at.iaik.suraq.smtsolver.SMTSolver;
import at.iaik.suraq.util.DebugHelper;
import at.iaik.suraq.util.Timer;

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
     * Stores the partition for which this parser is used.
     */
    private final int partition;

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
     * @param partition
     *            the partition for which this parser is used (1 to n).
     */
    public TseitinParser(SExpression root, Set<DomainVariable> domainVars,
            Set<PropositionalVariable> propsitionalVars,
            Set<ArrayVariable> arrayVars,
            Set<UninterpretedFunction> uninterpretedFunctions, int partition) {

        this.boolVariables = propsitionalVars;
        this.arrayVariables = arrayVars;
        this.domainVariables = domainVars;
        this.functions = uninterpretedFunctions;
        this.rootExpr = root;
        this.partition = partition;
    }

    /**
     * Parses the root s-expression into a formula, which can then be retrieved
     * using <code>getFormula</code>.
     * 
     * @see at.iaik.suraq.parser.Parser#parse()
     */
    @Override
    public void parse() throws ParseError {

        assert (rootExpr.getChildren().size() == 1);
        SExpression goalsExpr = rootExpr.getChildren().get(0);
        assert (goalsExpr.size() == 2);
        assert (goalsExpr.getChildren().get(0)
                .equals(SExpressionConstants.GOALS));
        SExpression goalExpr = goalsExpr.getChildren().get(1);
        assert (goalExpr.size() >= 2);
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
            clauses.add(parseFormulaBody(expr));
        }

        Map<Token, PropositionalVariable> renameMap = new HashMap<Token, PropositionalVariable>();
        List<PropositionalVariable> tmpList = new ArrayList<PropositionalVariable>(
                tseitinVariables.size());
        for (PropositionalVariable var : tseitinVariables) {
            PropositionalVariable newVar = new PropositionalVariable(
                    var.getVarName() + "_p!" + partition);
            renameMap.put(new Token(var.getVarName()), newVar);
            tmpList.add(newVar);
        }

        tseitinVariables.clear();
        tseitinVariables.addAll(tmpList);

        rootFormula = (new AndFormula(clauses)).substituteFormula(renameMap);
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
            formulaString = formulaString.replaceAll(token.toString()
                    + "[\\t\\n\\x0B\\f\\r(]", letDefinitions.get(token)
                    .toString());

        SExpression tmpExpr = SExpression.fromString(formulaString);

        return parseFormulaBody(tmpExpr);
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

        for (int i = 0; i < clauses.size(); i++) {
            Formula clause = clauses.get(i);
            if (clause instanceof OrFormula) {
                List<Integer> tseitinIndices = getTseitinVariablesFromFormula(clause);
                int numTseitinVars = tseitinIndices.size();
                if (numTseitinVars > 0) {
                    // check if current tseitin variable occurs in first or in
                    // the last literal
                    Formula firstLiteral = ((OrFormula) clause).getDisjuncts()
                            .get(0);
                    List<Integer> indicesFirstLit = getTseitinVariablesFromFormula(firstLiteral);
                    assert (indicesFirstLit.size() <= 1);

                    int numLiterals = ((OrFormula) clause).getDisjuncts()
                            .size();
                    Formula lastLiteral = ((OrFormula) clause).getDisjuncts()
                            .get(numLiterals - 1);
                    List<Integer> indicesLastLit = getTseitinVariablesFromFormula(lastLiteral);
                    assert (indicesLastLit.size() <= 1);

                    if (indicesFirstLit.contains(currTseitinIndex)
                            || indicesLastLit.contains(currTseitinIndex)) {
                        // check if clause doesn`t contain any larger idx
                        Collections.sort(tseitinIndices);
                        if (tseitinIndices.get(numTseitinVars - 1) <= currTseitinIndex) {
                            if (currClauses.size() == 0) {
                               /* System.out
                                        .println("INFO: Encoding Tseitin variable "
                                                + this.tseitinVariables.get(
                                                        currTseitinIndex)
                                                        .getVarName());
                                                        */
                                currClauses.add(clause);
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

                        Formula formula = buildTseitinFormula(currClauses,
                                currTseitinVar);

                        // calc partitions of tseitin variable
                        Set<Integer> partitions = formula
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

                        tseitinEncoding.put(new PropositionalVariable(
                                currTseitinVar.getVarName(), partition),
                                formula);

                        currTseitinIndex++;
                        currClauses = new ArrayList<Formula>();
                        i--; // re-check clause
                    }
                }
            }
        }

        return tseitinEncoding;
    }

    /**
     * Build the formula representing a tseiting variable.
     * 
     * @param CurrClauses
     *            clauses, from which the formula is build.
     * @param tseitinVar
     *            tseitin variable, for which a formula is build
     * 
     * @return the formula representing the tseitin variable
     */
    private Formula buildTseitinFormula(List<Formula> CurrClauses,
            PropositionalVariable tseitinVar) {

        //System.out.println("start build tseitin formula.");
        Timer buildTseitinFormulaTimer = new Timer();
        buildTseitinFormulaTimer.start();

        List<Formula> clauses = new ArrayList<Formula>(CurrClauses);

        Formula posFormula = buildPositiveFormula(clauses, tseitinVar);
        Formula negFormula = buildNegativeFormula(clauses, tseitinVar);
        assert (posFormula != null);
        assert (negFormula != null);
        while (!checkEquivalenceOfFormulas(posFormula, negFormula)) {
            clauses.remove(clauses.size() - 1); // remove last element from list
            posFormula = buildPositiveFormula(clauses, tseitinVar);
            negFormula = buildNegativeFormula(clauses, tseitinVar);
            assert (posFormula != null);
            assert (negFormula != null);
        }

        buildTseitinFormulaTimer.end();
        //System.out.println("finished build tseitin formula in "
        //        + buildTseitinFormulaTimer + ".\n");

        return posFormula;
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
     * @return returns true, if the two formulas imply each other.
     */
    public static boolean checkEquivalenceOfFormulas(Formula formula1,
            Formula formula2) {

        Set<DomainVariable> domainVars1 = formula1.getDomainVariables();
        Set<PropositionalVariable> propVars1 = formula1
                .getPropositionalVariables();
        Set<UninterpretedFunction> uif1 = formula1.getUninterpretedFunctions();

        Set<DomainVariable> domainVars2 = formula2.getDomainVariables();
        Set<PropositionalVariable> propVars2 = formula2
                .getPropositionalVariables();
        Set<UninterpretedFunction> uif2 = formula2.getUninterpretedFunctions();

        HashSet<DomainVariable> intersection = new HashSet<DomainVariable>(
                domainVars2);
        intersection.removeAll(domainVars1);

        if (!domainVars1.equals(domainVars2))
            return false;
        if (!propVars1.equals(propVars2))
            return false;
        if (!uif1.equals(uif2))
            return false;

        if (!checkFormulaImplication(formula1, formula2))
            return false;
        if (!checkFormulaImplication(formula2, formula1))
            return false;

        return true;
    }

    /**
     * Checks if the first formula implies the second formula.
     * 
     * @param formula1
     *            the first formula
     * 
     * @param formula2
     *            the second formula
     * 
     * @return returns true, the first formula implies the second formula.
     */
    public static boolean checkFormulaImplication(Formula formula1,
            Formula formula2) {
        List<Formula> conjuncts = new ArrayList<Formula>();
        conjuncts.add(formula1);
        conjuncts.add(new NotFormula(formula2));
        Formula formulaToCheck = new AndFormula(conjuncts);

        // Writes the declarations of all domain variables, propositional
        // variables and uninterpreted functions
        List<SExpression> outputExpressions = new ArrayList<SExpression>();

        outputExpressions.add(SExpressionConstants.SET_LOGIC_QF_UF);
        outputExpressions.add(SExpressionConstants.DECLARE_SORT_VALUE);

        Set<PropositionalVariable> allPropositionalVars = formula1
                .getPropositionalVariables();
        allPropositionalVars.addAll(formula2.getPropositionalVariables());

        Set<DomainVariable> allDomainVars = formula1.getDomainVariables();
        allDomainVars.addAll(formula2.getDomainVariables());

        Set<UninterpretedFunction> allFunctions = formula1
                .getUninterpretedFunctions();
        allFunctions.addAll(formula2.getUninterpretedFunctions());

        for (PropositionalVariable var : allPropositionalVars)
            outputExpressions
                    .add(SExpression.makeDeclareFun((Token) var.toSmtlibV2(),
                            SExpressionConstants.BOOL_TYPE, 0));

        for (DomainVariable var : allDomainVars)
            outputExpressions.add(SExpression.makeDeclareFun(
                    (Token) var.toSmtlibV2(), SExpressionConstants.VALUE_TYPE,
                    0));

        for (UninterpretedFunction function : allFunctions)
            outputExpressions.add(SExpression.makeDeclareFun(
                    function.getName(), function.getType(),
                    function.getNumParams()));

        outputExpressions.add(new SExpression(new Token("assert"), SExpression
                .fromString(formulaToCheck.toString())));

        outputExpressions.add(SExpressionConstants.CHECK_SAT);
        outputExpressions.add(SExpressionConstants.EXIT);

        String smtstr = "";
        for (SExpression exp : outputExpressions)
            smtstr += exp;

        SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type,
                SuraqOptions.getZ3Path());
        DebugHelper.getInstance().stringtoFile(smtstr, "debug-tseitin-check.txt");
        z3.solve(smtstr);

        switch (z3.getState()) {
        case SMTSolver.UNSAT:
            return true;
        case SMTSolver.SAT:
            return false;
        default:
            throw (new RuntimeException(
                    "Z3 tells us UNKOWN STATE. CHECK ERROR STREAM."));
        }

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

    /**
     * @see at.iaik.suraq.parser.SMTLibParser#parseFormulaBody(at.iaik.suraq.sexp.SExpression)
     */
    @Override
    protected Formula parseFormulaBody(SExpression expression)
            throws ParseError {
        if (isLet(expression))
            return handleLet(expression);
        else
            return super.parseFormulaBody(expression);
    }
}
