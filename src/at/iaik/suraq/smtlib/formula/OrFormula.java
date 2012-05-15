/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

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
     * Constructs a new <code>OrFormula</code>, consisting of the disjunction of
     * the given formulas.
     * 
     * @param formulas
     *            the formulas to disjunct.
     */
    public OrFormula(List<Formula> formulas) {
        super(formulas);
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

        for (int count = 0; count < formulas.size(); count++) {
            Formula formula = formulas.get(count).simplify();
            formulas.set(count, formula);

            if (formula instanceof PropositionalConstant) {
                if (((PropositionalConstant) formula).getValue()) {
                    return new PropositionalConstant(true);
                } else
                    formulas.remove(formula);
            }

            if (formula instanceof NotFormula) {
                if (((NotFormula) formula).isNegatedConstant() != null) {
                    if (!((NotFormula) formula).isNegatedConstant().getValue())
                        return new PropositionalConstant(true);
                }
                PropositionalVariable var = ((NotFormula) formula)
                        .isNegatedVariable();

                if (var != null) {
                    if (positiveVars.contains(var))
                        return new PropositionalConstant(true);
                    negativeVars.add(var);
                }

                if (formulas.contains(((NotFormula) formula)
                        .getNegatedFormula()))
                    return new PropositionalConstant(true);
            }

            if (formula instanceof PropositionalVariable) {
                if (negativeVars.contains(formula))
                    return new PropositionalConstant(true);
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
        return SExpressionConstants.OR;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm()
     */

    @Override
    public Formula transformToConsequentsForm() {
        return transformToConsequentsForm(false, true);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm(boolean,
     *      boolean)
     */

    public Formula transformToConsequentsForm(boolean notFlag,
            boolean firstLevel) {

        // Special case: not(or(literal)) --> or(not(literal))
        if (notFlag == true) {
            List<Formula> subFormulas = new ArrayList<Formula>();
            if (subFormulas.size() == 1)
                if (isLiteral(subFormulas.get(0))) {
                    List<Formula> literals = new ArrayList<Formula>();
                    literals.add(new NotFormula(subFormulas.get(0)));
                    return new OrFormula(literals);
                }
        }

        if (notFlag == true)
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
                        subFormulas.add(transformedSubFormula);
                    }
                } else {
                    Formula transformedSubFormula = subFormula
                            .transformToConsequentsForm(notFlag, false);

                    subFormulas.add(transformedSubFormula);
                }
            } else
                throw new RuntimeException(
                        "Unexpected Chid: Child of an OR Formula is not valid");

        }

        Formula orFormula = new OrFormula(subFormulas);
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
        if (isLiteral(formula))
            return true;
        return false;
    }

    /**
     * Checks if a given Formula is a literal. A literal is either an atom or a
     * negation of an atom.
     * 
     * @param formula
     *            formula to check
     * @return true, iff formula is an literal
     */
    public boolean isLiteral(Formula formula) {
        if (formula instanceof NotFormula) {
            Formula negatedFormula = ((NotFormula) formula).getNegatedFormula();
            return isAtom(negatedFormula);
        }
        return isAtom(formula);
    }

    /**
     * Checks if a given Formula is an atom. An atom is either a
     * <code>EqualityFormula</code>, a <code>PropositionalVariable</code>, a
     * <code>PropositionalConstant</code> or a
     * <code>UninterpretedPredicateInstance</code>.
     * 
     * @param formula
     *            formula to check
     * @return true, iff formula is atom
     * 
     */
    public boolean isAtom(Formula formula) {
        if (formula instanceof EqualityFormula)
            return true;
        if (formula instanceof PropositionalVariable)
            return true;
        if (formula instanceof PropositionalConstant)
            return true;
        if (formula instanceof UninterpretedPredicateInstance)
            return true;
        return false;
    }

}
