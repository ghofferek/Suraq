/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.parser;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.formula.Formula;
import at.iaik.suraq.sexp.SExpression;

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
        // TODO Auto-generated method stub

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
