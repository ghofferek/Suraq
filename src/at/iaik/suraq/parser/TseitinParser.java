/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.parser;

import java.util.ArrayList;
import java.util.HashMap;
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

        /*
         * (goals (goal (or d k!0) (or a k!0) (or (not d) (not a) (not k!0)) (or
         * a k!1) (or (not c) k!1) (or (not a) c (not k!1)) (or k!1 k!2) (or b
         * k!2) (or (not e) k!2) (or a k!2) (or c k!2) (or k!0 k!2) (or (not
         * k!1) (not b) e (not a) (not c) (not k!0) (not k!2)) (or (not k!2) a
         * b) :precision precise :depth 3) ) sat
         */
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
            clauses.add(parseFormulaBody(expr));
        }
        rootFormula = new AndFormula(clauses);
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

        boolean start = true;

        for (Formula clause : clauses) {
            // if clause has this form: (or d k!0), than it is part of formula
            // of a tseitin variable

            if (clause instanceof OrFormula) {
                if (((OrFormula) clause).getDisjuncts().size() == 2) {
                    Formula literal2 = ((OrFormula) clause).getDisjuncts().get(
                            1);
                    if (this.tseitinVariables.contains(literal2))
                        if (start = false) { // start new formula of a tseitin
                                             // variable
                            start = true;
                        } else { // add clause to formula of a tseitin variable

                        }

                } else {// Or Formula has more clausels

                }
            }

        }

        return tseitinEncoding;
    }
}
