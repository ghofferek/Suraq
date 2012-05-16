/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.List;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.proof.AnnotatedProofNode;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;

/**
 * 
 * Collection of (static) utility methods.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class Util {

    /**
     * Chooses a fresh variable name with respect to the given formula. The name
     * is also distinct from present macro names and uninterpreted function
     * names.
     * 
     * @param formula
     *            the formula
     * @param prefix
     *            a prefix that should be included in the variable name
     * @return a fresh variable name (w.r.t.<code>formula</code>), starting with
     *         <code>prefix</code>.
     */
    public static final String freshVarName(Formula formula, String prefix) {
        Set<ArrayVariable> arrayVars = formula.getArrayVariables();
        Set<DomainVariable> domainVars = formula.getDomainVariables();
        Set<PropositionalVariable> propVars = formula
                .getPropositionalVariables();
        Set<String> functionNames = formula.getUninterpretedFunctionNames();
        Set<String> macroNames = formula.getFunctionMacroNames();

        int count = -1;
        while (++count >= 0) {
            String name = prefix + (count > 0 ? ("_fresh" + count) : "");
            if (arrayVars.contains(new ArrayVariable(name)))
                continue;
            if (domainVars.contains(new DomainVariable(name)))
                continue;
            if (propVars.contains(new PropositionalVariable(name)))
                continue;
            if (functionNames.contains(name))
                continue;
            if (macroNames.contains(name))
                continue;
            return name;
        }
        throw new RuntimeException("Could not create fresh variable name.");
    }

    /**
     * Checks whether the given formula contains any of the given tokens as
     * identifiers.
     * 
     * @param formula
     *            the formula to check
     * @param names
     *            the <code>Token</code>s to check the formula against.
     * @return <code>true</code> if at least one of the <code>Token</code>s from
     *         <code>names</code>, occurred in <code>formula</code>,
     *         <code>false</code> otherwise.
     */
    public static final boolean formulaContainsAny(Formula formula,
            Set<Token> names) {
        Set<ArrayVariable> arrayVars = formula.getArrayVariables();
        Set<DomainVariable> domainVars = formula.getDomainVariables();
        Set<PropositionalVariable> propVars = formula
                .getPropositionalVariables();
        Set<String> functionNames = formula.getUninterpretedFunctionNames();
        Set<String> macroNames = formula.getFunctionMacroNames();

        for (Token token : names) {
            if (arrayVars.contains(new ArrayVariable(token)))
                return true;
            if (domainVars.contains(new DomainVariable(token)))
                return true;
            if (propVars.contains(new PropositionalVariable(token)))
                return true;
            if (functionNames.contains(token))
                return true;
            if (macroNames.contains(token))
                return true;
        }
        return false;
    }

    /**
     * Checks whether the given term contains any of the given tokens as
     * identifiers.
     * 
     * @param term
     *            the term to check
     * @param names
     *            the <code>Token</code>s to check the formula against.
     * @return <code>true</code> if at least one of the <code>Token</code>s from
     *         <code>names</code>, occurred in <code>term</code>,
     *         <code>false</code> otherwise.
     */
    public static final boolean termContainsAny(Term term, Set<Token> names) {
        Set<ArrayVariable> arrayVars = term.getArrayVariables();
        Set<DomainVariable> domainVars = term.getDomainVariables();
        Set<PropositionalVariable> propVars = term.getPropositionalVariables();
        Set<String> functionNames = term.getUninterpretedFunctionNames();
        Set<String> macroNames = term.getFunctionMacroNames();

        for (Token token : names) {
            if (arrayVars.contains(new ArrayVariable(token)))
                return true;
            if (domainVars.contains(new DomainVariable(token)))
                return true;
            if (propVars.contains(new PropositionalVariable(token)))
                return true;
            if (functionNames.contains(token))
                return true;
            if (macroNames.contains(token))
                return true;
        }
        return false;
    }

    /**
     * Chooses a fresh variable name w.r.t. the given formula.
     * 
     * @param formula
     *            the formula.
     * @return a fresh variable name w.r.t. <code>formula</code>
     */
    public static final String freshVarName(Formula formula) {
        return Util.freshVarName(formula, "");
    }

    /**
     * Increments the given list of (modular) counters.
     * 
     * @param counters
     *            the list of counters
     * @param modulus
     *            the modulus
     * @return <code>true</code> if the counters did not (overall) overflow,
     *         <code>false</code> otherwise.
     */
    public static boolean incrementCounters(List<Integer> counters, int modulus) {
        int count = 0;
        do {
            assert (counters.get(count) < modulus);
            if (counters.get(count) == modulus - 1) {
                counters.set(count, 0);
                count++;
            } else {
                counters.set(count, counters.get(count) + 1);
                return true;
            }
        } while (count < counters.size());
        return false;
    }

    /**
     * Creates a new variable of the given type.
     * 
     * @param name
     *            the name of the variable
     * @param type
     *            the type of the variable
     * @return a new variable with name <code>name</code> and type
     *         <code>type</code>.
     * @throws SuraqException
     *             if the given <code>type</code> does not exist
     */
    public static Term variableFactory(Token name, Token type)
            throws SuraqException {
        if (type.equals(SExpressionConstants.BOOL_TYPE))
            return new PropositionalVariable(name);
        if (type.equals(SExpressionConstants.VALUE_TYPE))
            return new DomainVariable(name);
        if (type.equals(SExpressionConstants.ARRAY_TYPE))
            return new ArrayVariable(name);
        throw new SuraqException("Cannot create variable of type "
                + type.toString());
    }

    /**
     * Given a clause with a single literal, returns this literal. Fails
     * otherwise.
     * 
     * @param clause
     * @return the single literal
     */
    public static Formula getSingleLiteral(Formula clause) {
        Formula formula = clause.transformToConsequentsForm();
        assert (formula instanceof OrFormula);
        List<Formula> disjuncts = ((OrFormula) formula).getDisjuncts();
        assert (disjuncts.size() == 1);
        assert (Util.isLiteral(disjuncts.get(0)));
        return disjuncts.get(0);
    }

    /**
     * Given a single literal of the form f(a,...)=f(b,...) returns the
     * uninterpreted Function that is used. Fails with an assertion error if the
     * given literal is not of this form.
     * 
     * @param literal
     *            a literal in the style of the consequent of a monotonicity
     *            proof.
     * @return the uninterpreted function that is used in the given equality.
     */
    public static UninterpretedFunction getUninterpretedFunction(Formula literal) {
        assert (literal instanceof DomainEq);
        DomainEq equality = (DomainEq) literal;
        assert (equality.getTerms().size() == 2);
        assert ((equality.getTerms().get(0) instanceof UninterpretedFunctionInstance) || (equality
                .getTerms().get(0) instanceof UninterpretedPredicateInstance));
        assert ((equality.getTerms().get(1) instanceof UninterpretedFunctionInstance) || (equality
                .getTerms().get(1) instanceof UninterpretedPredicateInstance));
        if (equality.getTerms().get(0) instanceof UninterpretedFunctionInstance) {
            assert (equality.getTerms().get(1) instanceof UninterpretedFunctionInstance);
            UninterpretedFunctionInstance instance1 = (UninterpretedFunctionInstance) (equality
                    .getTerms().get(0));
            UninterpretedFunctionInstance instance2 = (UninterpretedFunctionInstance) (equality
                    .getTerms().get(1));
            UninterpretedFunction function = instance1.getFunction();
            assert (function.equals(instance2.getFunction()));
            return function;
        } else if (equality.getTerms().get(0) instanceof UninterpretedPredicateInstance) {
            assert (equality.getTerms().get(1) instanceof UninterpretedPredicateInstance);
            UninterpretedPredicateInstance instance1 = (UninterpretedPredicateInstance) (equality
                    .getTerms().get(0));
            UninterpretedPredicateInstance instance2 = (UninterpretedPredicateInstance) (equality
                    .getTerms().get(1));
            UninterpretedFunction function = instance1.getFunction();
            assert (function.equals(instance2.getFunction()));
            return function;
        }
        assert (false);
        return null;
    }

    /**
     * @param currentAnnotatedNode
     * @return the domain terms occuring in the given node, from left to right.
     */
    public static DomainTerm[] getDomainTerms(AnnotatedProofNode node) {
        if (node.numPremises() == 0)
            return (DomainTerm[]) ((EqualityFormula) (node.getConsequent()
                    .getConsequent())).getTerms().toArray();
        else {
            assert (node.numPremises() == 3);
            DomainTerm[] part1 = (DomainTerm[]) ((EqualityFormula) (node
                    .getPremise1().getConsequent())).getTerms().toArray();
            DomainTerm[] part2 = (DomainTerm[]) ((EqualityFormula) (node
                    .getPremise3().getConsequent())).getTerms().toArray();
            DomainTerm[] result = new DomainTerm[4];
            result[0] = part1[0];
            result[1] = part1[1];
            result[2] = part2[0];
            result[3] = part2[1];
            return result;
        }
    }

    /**
     * @param formula1
     * @param formula2
     * @return <code>true</code> iff the two formulas are of the form a!=b and
     *         b!=a.
     */
    public static boolean checkForFlippedDisequality(Formula formula1,
            Formula formula2) {
        if (!Util.isSingleLiteral(formula1))
            return false;
        if (!Util.isSingleLiteral(formula2))
            return false;

        Formula literal1 = Util.getSingleLiteral(formula1);
        Formula literal2 = Util.getSingleLiteral(formula2);

        if (!(literal1 instanceof DomainEq))
            return false;
        if (!(literal2 instanceof DomainEq))
            return false;

        if (((DomainEq) literal1).isEqual())
            return false;
        if (((DomainEq) literal2).isEqual())
            return false;

        assert (((DomainEq) literal1).getTerms().size() == 2);
        assert (((DomainEq) literal2).getTerms().size() == 2);

        DomainTerm term1 = (DomainTerm) ((DomainEq) literal1).getTerms().get(0);
        DomainTerm term2 = (DomainTerm) ((DomainEq) literal1).getTerms().get(1);

        if (!term1.equals(((DomainEq) literal2).getTerms().get(1)))
            return false;
        if (!term2.equals(((DomainEq) literal2).getTerms().get(0)))
            return false;

        return true;
    }

    /**
     * @return <code>true</code> if the given formula is only a single literal
     *         (encapsulated in an OR).
     */
    public static boolean isSingleLiteral(Formula formula) {
        if (!(formula instanceof OrFormula))
            return false;
        OrFormula orFormula = (OrFormula) formula;
        return orFormula.getDisjuncts().size() == 1;
    }

    /**
     * Removes negation from literal.
     * 
     * @param literal
     *            literal to make positive
     * @return the resulting atom
     * 
     */
    public static Formula makeLiteralPositive(Formula literal) {

        if (!Util.isLiteral(literal))
            throw new RuntimeException("given formula should be a literal");

        if (literal instanceof NotFormula) {
            literal = ((NotFormula) literal).getNegatedFormula();
        }

        if (!Util.isAtom(literal))
            throw new RuntimeException("given literal should be an atom");
        return literal;
    }

    /**
     * Invert given literal.
     * 
     * @param literal
     *            literal to invert
     * @return the inverted literal
     * 
     */
    public static Formula invertLiteral(Formula literal) {

        if (!Util.isLiteral(literal))
            throw new RuntimeException("given formula should be a literal");

        if (literal instanceof NotFormula) {
            return ((NotFormula) literal).getNegatedFormula();
        } else
            return new NotFormula(literal);

    }

    /**
     * Checks if a given Formula is a literal. A literal is either an atom or a
     * negation of an atom.
     * 
     * @param formula
     *            formula to check
     * @return true, iff formula is an literal
     */
    public static boolean isLiteral(Formula formula) {
        if (formula instanceof NotFormula) {
            Formula negatedFormula = ((NotFormula) formula).getNegatedFormula();
            return Util.isAtom(negatedFormula);
        }
        return Util.isAtom(formula);
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
    public static boolean isAtom(Formula formula) {
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

    public static boolean isNegativeLiteral(Formula formula) {
        return Util.isLiteral(formula) && !Util.isAtom(formula);
    }
}
