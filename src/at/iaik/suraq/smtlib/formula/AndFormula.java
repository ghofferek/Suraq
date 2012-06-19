/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.util.Util;

/**
 * 
 * A formula that is a conjunction of other formulas.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class AndFormula extends AndOrXorFormula {

    /**
     * 
     */
    private static final long serialVersionUID = 870670778366136999L;

    /**
     * 
     * Constructs a new <code>AndFormula</code>, consisting of the conjunction
     * of the given formulas.
     * 
     * @param formulas
     *            the formulas to conjunct.
     */
    public AndFormula(List<? extends Formula> formulas) {
        super(formulas);
    }

    /**
     * Returns a collection of the conjuncted formulas.
     * 
     * @return a collection of the conjuncted formulas. (Copy)
     */
    public List<Formula> getConjuncts() {
        return new ArrayList<Formula>(formulas);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        Set<PropositionalVariable> negativeVars = new HashSet<PropositionalVariable>();
        Set<PropositionalVariable> positiveVars = new HashSet<PropositionalVariable>();

        for (int count = 0; count < formulas.size(); count++) {
            Formula formula = formulas.get(count).simplify();
            formulas.set(count, formula);
            if (formula instanceof PropositionalConstant) {
                if (!((PropositionalConstant) formula).getValue()) {
                    return new PropositionalConstant(false);
                } else
                    formulas.remove(formula);
            }

            if (formula instanceof NotFormula) {
                if (((NotFormula) formula).isNegatedConstant() != null) {
                    if (((NotFormula) formula).isNegatedConstant().getValue())
                        return new PropositionalConstant(false);
                }
                PropositionalVariable var = ((NotFormula) formula)
                        .isNegatedVariable();

                if (var != null) {
                    if (positiveVars.contains(var))
                        return new PropositionalConstant(false);
                    negativeVars.add(var);
                }

                if (formulas.contains(((NotFormula) formula)
                        .getNegatedFormula()))
                    return new PropositionalConstant(false);
            }

            if (formula instanceof PropositionalVariable) {
                if (negativeVars.contains(formula))
                    return new PropositionalConstant(false);
                positiveVars.add((PropositionalVariable) formula);
            }
        }

        // No simplifications found
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.AndOrXorFormula#getOperator()
     */
    @Override
    protected Token getOperator() {
        return SExpressionConstants.AND;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm()
     */

    @Override
    public OrFormula transformToConsequentsForm() {
        return (OrFormula) transformToConsequentsForm(false, true);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformFormulaToConsequentsFormula(at.iaik.suraq.smtlib.formula.Formula,
     *      boolean, boolean)
     */
    @Override
    public Formula transformToConsequentsForm(boolean notFlag,
            boolean firstLevel) {

        if (notFlag == false)
            throw new RuntimeException(
                    "an AND Formula is only allowed to occur inside an NOT formula.\n So notFlag has to be true");

        // apply deMorgan rule: NOT (a AND b) <=> NOT a OR NOT b

        List<Formula> subFormulas = new ArrayList<Formula>();
        for (Formula subFormula : this.formulas) {
            if (isValidChild(subFormula)) {
                if (subFormula instanceof AndFormula) {
                    // remove nested AND Formula
                    ArrayList<Formula> conjuncts = (ArrayList<Formula>) ((AndFormula) subFormula)
                            .getConjuncts();
                    for (Formula conjunct : conjuncts) {
                        Formula transformedSubFormula = conjunct
                                .transformToConsequentsForm(notFlag, false);
                        subFormulas.add(transformedSubFormula);
                    }
                } else {
                    Formula transformedSubFormula = subFormula
                            .transformToConsequentsForm(notFlag, false);

                    subFormulas.add(transformedSubFormula);
                }
            } else
                throw new RuntimeException(
                        "Unexpected Chid: Child of an AND Formula can either be an AND Formula, NOT Formula or a Literal");

        }

        Formula orFormula = new OrFormula(subFormulas);
        return orFormula;
    }

    /**
     * Checks if a given Formula is a literal, or an AND Formula or a NOT
     * formula.
     * 
     * @param formula
     *            formula to check
     * @return true, iff formula is valid
     */
    public boolean isValidChild(Formula formula) {
        if (formula instanceof AndFormula)
            return true;
        if (formula instanceof NotFormula)
            return true;
        if (Util.isLiteral(formula))
            return true;
        return false;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.Map)
     */
    @Override
    public PropositionalVariable tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding) {

        assert (clauses != null);
        assert (encoding != null);

        Set<Integer> partitions = this.getPartitionsFromSymbols();
        assert (partitions.size() == 1 || partitions.size() == 2);
        if (partitions.size() == 2)
            partitions.remove(-1);
        assert (partitions.size() == 1);
        int partition = partitions.iterator().next();
        PropositionalVariable tseitinVar = Util.freshTseitinVar(partition);
        encoding.put(tseitinVar, this.deepFormulaCopy());

        List<Formula> disjuncts = new ArrayList<Formula>(formulas.size() + 1);

        for (Formula formula : formulas) {
            PropositionalVariable currentTseitinVar = formula.tseitinEncode(
                    clauses, encoding);

            disjuncts.add(new NotFormula(currentTseitinVar));

            List<Formula> tmp = new ArrayList<Formula>(2);
            tmp.add(new NotFormula(tseitinVar));
            tmp.add(currentTseitinVar);
            clauses.add(new OrFormula(tmp));
        }

        disjuncts.add(tseitinVar);
        clauses.add(new OrFormula(disjuncts));

        return tseitinVar;
    }

}
