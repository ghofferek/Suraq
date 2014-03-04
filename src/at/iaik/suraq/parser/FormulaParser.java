/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.parser;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;

/**
 * Used for parsing (single) formulas, e.g, after simplification.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class FormulaParser extends SMTLibParser {

    private Formula parsedFormula;

    private static final long serialVersionUID = 1L;

    /**
     * 
     * Constructs a new <code>FormulaParser</code>.
     * 
     * @param propVars
     * @param domainVars
     * @param arrayVars
     * @param uninterpretedFunctions
     * @param input
     * @throws IOException
     * @throws ParseError
     */
    public FormulaParser(Collection<? extends PropositionalVariable> propVars,
            Collection<? extends DomainVariable> domainVars,
            Collection<? extends ArrayVariable> arrayVars,
            Collection<? extends UninterpretedFunction> uninterpretedFunctions,
            BufferedReader input) throws IOException, ParseError {

        this.arrayVariables = new HashSet<ArrayVariable>(arrayVars);
        this.boolVariables = new HashSet<PropositionalVariable>(propVars);
        this.domainVariables = new HashSet<DomainVariable>(domainVars);
        this.functions = new HashSet<UninterpretedFunction>(
                uninterpretedFunctions);

        SExpParser sExpParser = new SExpParser(input);
        sExpParser.parse();
        assert (sExpParser.parsingSuccessfull);
        SExpression expression = sExpParser.getRootExpr();
        if (expression.getChildren().size() == 1)
            this.rootExpr = sExpParser.getRootExpr().getChildren().get(0);
        else
            this.rootExpr = sExpParser.getRootExpr();
    }

    /**
     * @see at.iaik.suraq.parser.Parser#parse()
     */
    @Override
    public void parse() throws ParseError {
        parsedFormula = this.parseFormulaBody(rootExpr);
    }

    /**
     * @return the <code>parsedFormula</code>
     */
    public Formula getParsedFormula() {
        return parsedFormula;
    }

}
