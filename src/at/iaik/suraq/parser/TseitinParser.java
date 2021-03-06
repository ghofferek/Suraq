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
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.util.Timer;
import at.iaik.suraq.util.Util;

/**
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */

public class TseitinParser extends SMTLibParser {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

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

        assert (goalExpr.getChildren().get(numChildren - 4).equals(Token
                .generate(":precision")));
        assert (goalExpr.getChildren().get(numChildren - 3).equals(Token
                .generate("precise")));
        assert (goalExpr.getChildren().get(numChildren - 2).equals(Token
                .generate(":depth")));

        goalExpr.removeChild(numChildren - 1);
        goalExpr.removeChild(numChildren - 2);
        goalExpr.removeChild(numChildren - 3);
        goalExpr.removeChild(numChildren - 4);
        // System.out.print(""+goalExpr.getChildren().size());

        List<Formula> clauses = new ArrayList<Formula>();
        List<SExpression> tmp = goalExpr.getChildren();
        int size = tmp.size();
        int step = size / 100 + 1;
        // chillebold: here are to many saved reads (> 2Mrd.) on DomainVar
        for (int i = 0; i < size; i++) {
            if (i % step == 0) {
                System.out.print(" " + (i / step) + "%");
                if ((i / step) % 10 == 9)
                    System.out.print("\n");
            }
            SExpression expr = tmp.get(i);
            clauses.add(parseFormulaBody(expr));
        }

        Map<Token, PropositionalVariable> renameMap = new HashMap<Token, PropositionalVariable>();
        List<PropositionalVariable> tmpList = new ArrayList<PropositionalVariable>(
                tseitinVariables.size());
        for (PropositionalVariable var : tseitinVariables) {
            PropositionalVariable newVar = PropositionalVariable.create(var
                    .getVarName() + "_p!" + partition);
            renameMap.put(Token.generate(var.getVarName()), newVar);
            tmpList.add(newVar);
        }

        tseitinVariables.clear();
        tseitinVariables.addAll(tmpList);

        rootFormula = (AndFormula.generate(clauses)).substituteFormula(
                renameMap, new HashMap<SMTLibObject, SMTLibObject>());
        parsingSuccessfull = true;
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
                                /*
                                 * System.out
                                 * .println("INFO: Encoding Tseitin variable " +
                                 * this.tseitinVariables.get( currTseitinIndex)
                                 * .getVarName());
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

                        tseitinEncoding
                                .put(PropositionalVariable.create(
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

        // System.out.println("start build tseitin formula.");
        Timer buildTseitinFormulaTimer = new Timer();
        buildTseitinFormulaTimer.start();

        List<Formula> clauses = new ArrayList<Formula>(CurrClauses);

        Formula posFormula = buildPositiveFormula(clauses, tseitinVar);
        Formula negFormula = buildNegativeFormula(clauses, tseitinVar);
        assert (posFormula != null);
        assert (negFormula != null);
        while (!Util.checkEquivalenceOfFormulas(posFormula, negFormula)) {
            clauses.remove(clauses.size() - 1); // remove last element from list
            posFormula = buildPositiveFormula(clauses, tseitinVar);
            negFormula = buildNegativeFormula(clauses, tseitinVar);
            assert (posFormula != null);
            assert (negFormula != null);
        }

        buildTseitinFormulaTimer.stop();
        // System.out.println("finished build tseitin formula in "
        // + buildTseitinFormulaTimer + ".\n");

        return posFormula;
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

            conjuncts.add(OrFormula.generate(literals));

        }
        return AndFormula.generate(conjuncts);
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

            disjuncts.add(NotFormula.create(OrFormula.generate(literals)));

        }
        return OrFormula.generate(disjuncts);
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

        Set<PropositionalVariable> propVars = new HashSet<PropositionalVariable>();
        formula.getPropositionalVariables(propVars, new HashSet<SMTLibObject>());

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
    public Formula parseFormulaBody(SExpression expression) throws ParseError {
        if (isLet(expression))
            return handleLet(expression);
        else
            return super.parseFormulaBody(expression);
    }
}
