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
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.Util;

/**
 * 
 * A formula that is a disjunction of other formulas.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class OrFormula extends AndOrXorFormula {

    /**
     * 
     */
    private static final long serialVersionUID = -1803216846463035758L;

    /**
     * 
     * Constructs a new <code>OrFormula</code>, consisting of the disjunction of
     * the given formulas.
     * 
     * @param formulas
     *            the formulas to disjunct.
     */
    public OrFormula(List<Formula> formulas) {
        super(formulas);
    }

    public static OrFormula generate(List<Formula> formulas) {
        // return FormulaCache.orFormula.put(new OrFormula(formulas));
        return (OrFormula) FormulaCache.andOrXorFormula.put(new OrFormula(
                formulas));
    }

    /**
     * Returns a collection of the disjuncted formulas.
     * 
     * @return a collection of the disjuncted formulas. (Copy)
     */
    public List<Formula> getDisjuncts() {
        return new ArrayList<Formula>(formulas);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        Set<PropositionalVariable> negativeVars = new HashSet<PropositionalVariable>();
        Set<PropositionalVariable> positiveVars = new HashSet<PropositionalVariable>();

        ArrayList<Formula> formulas = new ArrayList<Formula>(this.formulas);
        for (int count = 0; count < formulas.size(); count++) {
            Formula formula = formulas.get(count).simplify();
            formulas.set(count, formula);

            if (formula instanceof PropositionalConstant) {
                if (((PropositionalConstant) formula).getValue()) {
                    return PropositionalConstant.create(true);
                } else
                    formulas.remove(formula);
            }

            if (formula instanceof NotFormula) {
                if (((NotFormula) formula).isNegatedConstant() != null) {
                    if (!((NotFormula) formula).isNegatedConstant().getValue())
                        return PropositionalConstant.create(true);
                }
                PropositionalVariable var = ((NotFormula) formula)
                        .isNegatedVariable();

                if (var != null) {
                    if (positiveVars.contains(var))
                        return PropositionalConstant.create(true);
                    negativeVars.add(var);
                }

                if (formulas.contains(((NotFormula) formula)
                        .getNegatedFormula()))
                    return PropositionalConstant.create(true);
            }

            if (formula instanceof PropositionalVariable) {
                if (negativeVars.contains(formula))
                    return PropositionalConstant.create(true);
                positiveVars.add((PropositionalVariable) formula);
            }
        }

        // No simplifications found
        return create(formulas);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.AndOrXorFormula#getOperator()
     */
    @Override
    protected Token getOperator() {
        return SExpressionConstants.OR;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm()
     */

    @Override
    public OrFormula transformToConsequentsForm() {
        return (OrFormula) transformToConsequentsForm(false, true);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm(boolean,
     *      boolean)
     */

    @Override
    public Formula transformToConsequentsForm(boolean notFlag,
            boolean firstLevel) {
        // Special case: not(or(Literal)) --> or(not(literal)
        if ((notFlag == true) && (this.formulas.size() != 1))
            throw new RuntimeException(
                    "an Or Formula is not allowed to occur inside an NOT formula.\n So notFlag has to be false");

        List<Formula> subFormulas = new ArrayList<Formula>();
        for (Formula subFormula : this.formulas) {
            if (isValidChild(subFormula)) {

                if (subFormula instanceof OrFormula) {
                    // remove nested OR Formula
                    ArrayList<Formula> disjuncts = (ArrayList<Formula>) ((OrFormula) subFormula)
                            .getDisjuncts();
                    for (Formula disjunct : disjuncts) {
                        Formula transformedSubFormula = disjunct
                                .transformToConsequentsForm(notFlag, false);

                        if (!subFormulas.contains(transformedSubFormula))
                            subFormulas.add(transformedSubFormula);
                    }
                } else {

                    Formula transformedSubFormula = subFormula
                            .transformToConsequentsForm(notFlag, false);
                    if (!subFormulas.contains(transformedSubFormula))
                        subFormulas.add(transformedSubFormula);
                }
            } else
                throw new RuntimeException(
                        "Unexpected Chid: Child of an OR Formula is not valid");

        }

        Formula orFormula = OrFormula.generate(subFormulas);
        return orFormula;
    }

    /**
     * Checks if a given formula is a valid child of a OR formula
     * 
     * @param formula
     *            formula to check
     * @return true, iff formula is valid
     */
    public boolean isValidChild(Formula formula) {
        if (formula instanceof OrFormula)
            return true;
        if (formula instanceof NotFormula)
            return true;
        if (formula instanceof ImpliesFormula)
            return true;
        if (Util.isLiteral(formula))
            return true;
        return false;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.List,
     *      java.util.Map)
     */
    @Override
    public PropositionalVariable tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding,
            Map<Formula, PropositionalVariable> done, int partition) {
        assert (clauses != null);
        assert (encoding != null);
        assert (done != null);
        if (done.get(this) != null)
            return done.get(this);

        Set<Integer> partitions = this.getPartitionsFromSymbols();
        assert (partitions.size() == 1 || partitions.size() == 2);
        if (partitions.size() == 2)
            partitions.remove(-1);
        assert (partitions.size() == 1);
        assert (partitions.iterator().next().equals(partition) || partitions
                .iterator().next().equals(-1));

        PropositionalVariable tseitinVar = Util.freshTseitinVar(partition);

        List<Formula> disjuncts = new ArrayList<Formula>(formulas.size() + 1);
        encoding.put(tseitinVar, this.deepFormulaCopy());
        done.put(this, tseitinVar);

        for (Formula formula : formulas) {
            Formula currentTseitinVar = formula.tseitinEncode(clauses,
                    encoding, done, partition);
            assert (Util.isLiteral(currentTseitinVar));

            disjuncts.add(currentTseitinVar);

            List<Formula> tmp = new ArrayList<Formula>(2);
            tmp.add(NotFormula.create(currentTseitinVar));
            tmp.add(tseitinVar);
            clauses.add(OrFormula.generate(tmp));
        }

        disjuncts.add(NotFormula.create(tseitinVar));
        clauses.add(OrFormula.generate(disjuncts));

        return tseitinVar;
    }

}
