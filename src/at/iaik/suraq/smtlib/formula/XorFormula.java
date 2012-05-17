/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * 
 * A formula that is the xor of other formulas.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class XorFormula extends AndOrXorFormula {

    /**
     * 
     * Constructs a new <code>XorFormula</code>, consisting of the xor of the
     * given formulas.
     * 
     * @param formulas
     *            the formulas to xor.
     */
    public XorFormula(List<Formula> formulas) {
        super(formulas);
    }

    /**
     * Converts this formula into an equivalent formula, using only AND and OR.
     * Subformulas are not copied.
     * 
     * @return an equivalent and/or-formula.
     */
    public OrFormula toAndOrFormula() {
        Formula x1 = formulas.get(0);
        Formula x2 = (new XorFormula(formulas.subList(1, formulas.size())))
                .toAndOrFormula();
        List<Formula> listAnd1 = new ArrayList<Formula>();
        List<Formula> listAnd2 = new ArrayList<Formula>();
        List<Formula> listOr = new ArrayList<Formula>();
        listAnd1.add(new NotFormula(x1));
        listAnd1.add(x2);
        AndFormula and1 = new AndFormula(listAnd1);
        listAnd2.add(new NotFormula(x2));
        listAnd2.add(x1);
        AndFormula and2 = new AndFormula(listAnd2);
        listOr.add(and1);
        listOr.add(and2);
        return new OrFormula(listOr);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.AndOrXorFormula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        return toAndOrFormula().negationNormalForm();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.AndOrXorFormula#getOperator()
     */
    @Override
    protected Token getOperator() {
        return SExpressionConstants.XOR;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm()
     */
    @Override
    public OrFormula transformToConsequentsForm() {
        throw new RuntimeException(
                "transformToConsequentsForm cannot be called on a Xor Formula.\n"
                        + "Xor Formulas should not occur in the consequents of a proof.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm(boolean,
     *      boolean)
     */
    @Override
    public Formula transformToConsequentsForm(boolean notFlag,
            boolean firstLevel) {
        throw new RuntimeException(
                "transformToConsequentsForm cannot be called on a Xor Formula.\n"
                        + "Xor Formulas should not occur in the consequents of a proof.");
    }
}
