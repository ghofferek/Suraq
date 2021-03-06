/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.math.BigInteger;
import java.text.DateFormat;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Pattern;

import at.iaik.suraq.exceptions.IncomparableTermsException;
import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.parser.LogicParser;
import at.iaik.suraq.parser.SExpParser;
import at.iaik.suraq.proof.AnnotatedProofNode;
import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.resProof.Clause;
import at.iaik.suraq.resProof.Literal;
import at.iaik.suraq.resProof.ResNode;
import at.iaik.suraq.resProof.ResProof;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.smtlib.TransformedZ3Proof;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.FormulaTerm;
import at.iaik.suraq.smtlib.formula.FunctionMacro;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.smtlib.formula.PropositionalEq;
import at.iaik.suraq.smtlib.formula.PropositionalTerm;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.smtsolver.SMTSolver;

/**
 * 
 * Collection of (static) utility methods.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public final class Util {

    private static Map<String, Integer> literalsID = new HashMap<String, Integer>();
    private static Map<Integer, ResNode> resNodes = new HashMap<Integer, ResNode>();
    private static ResProof resProof;
    private static Map<Integer, Formula> literalMap = new HashMap<Integer, Formula>();

    public static final DecimalFormat byteAmountFormatter = new DecimalFormat(
            "000,000,000,000");

    public static final DecimalFormat largeNumberFormatter = new DecimalFormat(
            "###,###,###,###");

    public static final DecimalFormat veryLargeNumberFormatter = new DecimalFormat(
            "###,###,###,###,###,###");

    /**
     * Counts the number of Tseitin vars that have been introduced so far. This
     * makes sure they all get a unique name.
     */
    private static int tseitinVarCounter = 0;

    public static final Pattern digitsPattern = Pattern
            .compile("([0-9]+)(\\z|[^0-9])");

    /**
     * 
     * @param partition
     *            the assert partition with which the variable will be
     *            associated.
     * @return a Tseitin variable with a name that has not been returned before.
     */
    public static PropositionalVariable freshTseitinVar(int partition) {
        return PropositionalVariable.create("ts!" + Util.tseitinVarCounter++,
                partition);
    }

    /**
     * This resets the counter that is used to make Tseitin-variables unique.
     * Only call if you know what you are doing (like executing multiple test
     * cases with different <code>Suraq</code> objects).
     */
    public static void resetTseitinCounter() {
        Util.tseitinVarCounter = 0;
    }

    private static Formula lastFormula = null;
    private static final Set<String> lostNames = new HashSet<String>();

    public static final String freshVarNameCached(Formula formula, String prefix) {
        return Util.freshVarNameCached(formula, prefix, null);
    }

    public static final String freshVarNameCached(Formula formula,
            String prefix, Set<String> instances) {
        if (Util.lastFormula != formula) {
            // System.out.println("*** New Formula detected. Building lostNames.");
            Util.lastFormula = formula;
            Util.lostNames.clear();
            // hashcode must be varname.hashcode() !!!
            Set<SMTLibObject> done = new HashSet<SMTLibObject>();
            Set<ArrayVariable> aVars = new HashSet<ArrayVariable>();
            formula.getArrayVariables(aVars, done);
            done.clear();
            Set<PropositionalVariable> pVars = new HashSet<PropositionalVariable>();
            formula.getPropositionalVariables(pVars, done);
            done.clear();
            Set<DomainVariable> dVars = new HashSet<DomainVariable>();
            formula.getDomainVariables(dVars, done);
            done.clear();
            Set<UninterpretedFunction> ufs = new HashSet<UninterpretedFunction>();
            formula.getUninterpretedFunctions(ufs, done);
            done.clear();
            Set<FunctionMacro> macros = new HashSet<FunctionMacro>();
            formula.getFunctionMacros(macros, done);
            done.clear();

            for (ArrayVariable aVar : aVars)
                Util.lostNames.add(aVar.getVarName());
            for (DomainVariable dVar : dVars)
                Util.lostNames.add(dVar.getVarName());

            for (PropositionalVariable pVar : pVars)
                Util.lostNames.add(pVar.getVarName());

            for (UninterpretedFunction uf : ufs)
                Util.lostNames.add(uf.getName().toString());

            for (FunctionMacro macro : macros)
                Util.lostNames.add(macro.getName().toString());
        }

        int count = -1;
        while (++count >= 0) {
            String name = prefix + (count > 0 ? ("_fresh" + count) : "");

            if (Util.lostNames.contains(name))
                continue;
            if (instances != null && instances.contains(name))
                continue;
            Util.lostNames.add(name);
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
        Set<SMTLibObject> done = new HashSet<SMTLibObject>();
        Set<ArrayVariable> aVars = new HashSet<ArrayVariable>();
        formula.getArrayVariables(aVars, done);
        done.clear();
        Set<PropositionalVariable> pVars = new HashSet<PropositionalVariable>();
        formula.getPropositionalVariables(pVars, done);
        done.clear();
        Set<DomainVariable> dVars = new HashSet<DomainVariable>();
        formula.getDomainVariables(dVars, done);
        done.clear();
        Set<String> ufs = new HashSet<String>();
        formula.getUninterpretedFunctionNames(ufs, done);
        done.clear();
        Set<String> macros = new HashSet<String>();
        formula.getFunctionMacroNames(macros, done);
        done.clear();

        for (Token token : names) {
            if (aVars.contains(ArrayVariable.create(token)))
                return true;
            if (dVars.contains(DomainVariable.create(token)))
                return true;
            if (pVars.contains(PropositionalVariable.create(token)))
                return true;
            if (ufs.contains(token.toString()))
                return true;
            if (macros.contains(token.toString()))
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
        Set<SMTLibObject> done = new HashSet<SMTLibObject>();
        Set<ArrayVariable> aVars = new HashSet<ArrayVariable>();
        term.getArrayVariables(aVars, done);
        done.clear();
        Set<PropositionalVariable> pVars = new HashSet<PropositionalVariable>();
        term.getPropositionalVariables(pVars, done);
        done.clear();
        Set<DomainVariable> dVars = new HashSet<DomainVariable>();
        term.getDomainVariables(dVars, done);
        done.clear();
        Set<String> ufs = new HashSet<String>();
        term.getUninterpretedFunctionNames(ufs, done);
        done.clear();
        Set<String> macros = new HashSet<String>();
        term.getFunctionMacroNames(macros, done);
        done.clear();

        for (Token token : names) {
            if (aVars.contains(ArrayVariable.create(token)))
                return true;
            if (dVars.contains(DomainVariable.create(token)))
                return true;
            if (pVars.contains(PropositionalVariable.create(token)))
                return true;
            if (ufs.contains(token.toString()))
                return true;
            if (macros.contains(token.toString()))
                return true;
        }
        return false;
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
            return PropositionalVariable.create(name);
        if (type.equals(SExpressionConstants.VALUE_TYPE))
            return DomainVariable.create(name);
        if (type.equals(SExpressionConstants.ARRAY_TYPE))
            return ArrayVariable.create(name);
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
        if (clause == null)
            return null;
        if (!(clause instanceof OrFormula)) {
            assert (Util.isLiteral(clause));
            return clause;
        }
        assert (clause instanceof OrFormula);
        List<Formula> disjuncts = ((OrFormula) clause).getDisjuncts();
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
    public static UninterpretedFunction getUninterpretedFunctionOrPredicate(
            Formula literal) {
        assert (literal instanceof EqualityFormula);
        EqualityFormula equality = (EqualityFormula) literal;
        assert (equality.getTerms().size() == 2);
        assert ((equality.getTerms().get(0) instanceof UninterpretedFunctionInstance) || (equality
                .getTerms().get(0) instanceof PropositionalTerm));
        assert ((equality.getTerms().get(1) instanceof UninterpretedFunctionInstance) || (equality
                .getTerms().get(1) instanceof PropositionalTerm));
        if (equality.getTerms().get(0) instanceof UninterpretedFunctionInstance) {
            assert (equality.getTerms().get(1) instanceof UninterpretedFunctionInstance);
            UninterpretedFunctionInstance instance1 = (UninterpretedFunctionInstance) (equality
                    .getTerms().get(0));
            UninterpretedFunctionInstance instance2 = (UninterpretedFunctionInstance) (equality
                    .getTerms().get(1));
            UninterpretedFunction function = instance1.getFunction();
            assert (function.equals(instance2.getFunction()));
            return function;
        } else if (equality.getTerms().get(0) instanceof PropositionalTerm) {
            assert (equality.getTerms().get(1) instanceof PropositionalTerm);

            UninterpretedPredicateInstance instance1 = null;
            if (equality.getTerms().get(0) instanceof FormulaTerm) {
                FormulaTerm term1 = (FormulaTerm) equality.getTerms().get(0);
                instance1 = (UninterpretedPredicateInstance) term1.getFormula();
            } else {
                assert (equality.getTerms().get(0) instanceof UninterpretedPredicateInstance);
                instance1 = (UninterpretedPredicateInstance) equality
                        .getTerms().get(0);
            }
            assert (instance1 != null);

            UninterpretedPredicateInstance instance2 = null;
            if (equality.getTerms().get(1) instanceof FormulaTerm) {
                FormulaTerm term2 = (FormulaTerm) equality.getTerms().get(1);
                instance2 = (UninterpretedPredicateInstance) term2.getFormula();
            } else {
                assert (equality.getTerms().get(1) instanceof UninterpretedPredicateInstance);
                instance2 = (UninterpretedPredicateInstance) equality
                        .getTerms().get(1);
            }
            assert (instance2 != null);

            UninterpretedFunction function = instance1.getFunction();
            assert (function.equals(instance2.getFunction()));
            return function;
        }
        assert (false);
        return null;
    }

    /**
     * @param currentAnnotatedNode
     * @return the domain terms occurring in the given node, from left to right.
     */
    public static DomainTerm[] getDomainTerms(AnnotatedProofNode node) {
        if (node.numPremises() == 0) {
            DomainTerm[] result = new DomainTerm[2];
            Object[] tmp = ((EqualityFormula) Util.getSingleLiteral((node
                    .getConsequent().getConsequent()))).getTerms().toArray();
            assert (tmp.length == 2);
            for (int count = 0; count < 2; count++) {
                assert (tmp[count] != null);
                assert (tmp[count] instanceof DomainTerm);
                result[count] = (DomainTerm) tmp[count];
            }
            return result;
        } else {
            assert (node.numPremises() == 3);
            Object[] part1 = ((EqualityFormula) Util.getSingleLiteral((node
                    .getPremise1().getConsequent()))).getTerms().toArray();
            Object[] part2 = ((EqualityFormula) Util.getSingleLiteral((node
                    .getPremise3().getConsequent()))).getTerms().toArray();
            DomainTerm[] result = new DomainTerm[4];
            result[0] = (DomainTerm) part1[0];
            result[1] = (DomainTerm) part1[1];
            result[2] = (DomainTerm) part2[0];
            result[3] = (DomainTerm) part2[1];
            for (int count = 0; count < 4; count++)
                assert (result[count] != null);
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
        return Util.checkForFlippedEquality(formula1, formula2, false);
    }

    /**
     * @param formula1
     * @param formula2
     * @return <code>true</code> iff the two formulas are of the form a!=b and
     *         b!=a or a==b and b==a.
     */
    public static boolean checkForFlippedEqualityOrDisequality(
            Formula formula1, Formula formula2) {
        if (Util.checkForFlippedEquality(formula1, formula2, true))
            return true;
        if (Util.checkForFlippedEquality(formula1, formula2, false))
            return true;
        return false;
    }

    /**
     * @param formula1
     * @param formula2
     * @param equal
     *            if <code>true</code>, check for positive equalities, else for
     *            disequalities.
     * @return <code>true</code> iff the two formulas are of the form a R b and
     *         b R a, where R is either <code>==</code> (if <code>equal</code>
     *         is true, or <code>!=</code> otherwise.
     */
    public static boolean checkForFlippedEquality(Formula formula1,
            Formula formula2, boolean equal) {
        if (!Util.isLiteral(formula1))
            return false;
        if (!Util.isLiteral(formula2))
            return false;

        Formula literal1 = Util.getSingleLiteral(formula1);
        Formula literal2 = Util.getSingleLiteral(formula2);

        if (!(Util.makeLiteralPositive(literal1) instanceof EqualityFormula))
            return false;
        if (!(Util.makeLiteralPositive(literal2) instanceof EqualityFormula))
            return false;

        if (!Util.isNegativeLiteral(literal1) ^ equal)
            return false;
        if (!Util.isNegativeLiteral(literal2) ^ equal)
            return false;

        literal1 = Util.makeLiteralPositive(literal1);
        literal2 = Util.makeLiteralPositive(literal2);

        assert (((EqualityFormula) literal1).isEqual());
        assert (((EqualityFormula) literal2).isEqual());

        assert (((EqualityFormula) literal1).getTerms().size() == 2);
        assert (((EqualityFormula) literal2).getTerms().size() == 2);

        Term term1 = ((EqualityFormula) literal1).getTerms().get(0);
        Term term2 = ((EqualityFormula) literal1).getTerms().get(1);

        if (!term1.equals(((EqualityFormula) literal2).getTerms().get(1)))
            return false;
        if (!term2.equals(((EqualityFormula) literal2).getTerms().get(0)))
            return false;

        return true;
    }

    /**
     * @return <code>true</code> if the given formula is only a single literal
     *         (encapsulated in an OR).
     */
    public static boolean isUnitClause(Formula formula) {
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

        literal = Util.getSingleLiteral(literal);
        if (literal instanceof NotFormula) {
            return ((NotFormula) literal).getNegatedFormula();
        } else
            return NotFormula.create(literal);

    }

    /**
     * Checks if a given Formula is a literal. A literal is either an atom or a
     * negation of an atom. Also handles unit clauses.
     * 
     * @param formula
     *            formula to check
     * @return true, iff formula is an literal or a unit clause
     */
    public static boolean isLiteral(Formula formula) {

        if (formula instanceof FormulaTerm)
            formula = ((FormulaTerm) formula).getFormula();

        if (formula instanceof OrFormula) {
            if (((OrFormula) formula).getDisjuncts().size() != 1)
                return false;
            formula = ((OrFormula) formula).getDisjuncts().get(0);
        }
        if (formula instanceof NotFormula) {
            formula = ((NotFormula) formula).getNegatedFormula();
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

        if (formula instanceof FormulaTerm)
            formula = ((FormulaTerm) formula).getFormula();

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

    /**
     * @param clause1
     * @param clause2
     * @return the resolving literal in positive form, or <code>null</code> if
     *         no such literal exists.
     */
    public static Formula findResolvingLiteral(OrFormula clause1,
            OrFormula clause2) {
        for (Formula formula : clause1.getDisjuncts()) {
            assert (Util.isLiteral(formula));
            Formula inverseLiteral = Util.invertLiteral(formula);
            if (clause2.getDisjuncts().contains(inverseLiteral))
                return Util.makeLiteralPositive(inverseLiteral);
            else if (Util.makeLiteralPositive(inverseLiteral) instanceof EqualityFormula) {
                EqualityFormula reverseLiteral = Util
                        .reverseEquality((EqualityFormula) (Util
                                .makeLiteralPositive(inverseLiteral)));
                Formula reverseInverseLiteral = null;
                if (Util.isNegativeLiteral(inverseLiteral))
                    reverseInverseLiteral = NotFormula.create(reverseLiteral);
                else
                    reverseInverseLiteral = reverseLiteral;
                if (clause2.getDisjuncts().contains(reverseInverseLiteral))
                    return Util.makeLiteralPositive(reverseInverseLiteral);
            }

        }
        return null;
    }

    /**
     * Finds the resolving literal between the given proof nodes.
     * 
     * @param subProofs
     *            must be of size 2.
     * @return the resolving literal (in positive form), or <code>null</code> if
     *         no such literal exists.
     */
    public static Formula findResolvingLiteral(
            Collection<VeritProofNode> subProofs) {
        assert (subProofs != null);
        assert (subProofs.size() == 2);
        Iterator<VeritProofNode> iterator = subProofs.iterator();
        assert (iterator.hasNext());
        VeritProofNode node1 = iterator.next();
        assert (iterator.hasNext());
        VeritProofNode node2 = iterator.next();
        assert (node1 != null);
        assert (node2 != null);
        assert (!iterator.hasNext());
        return Util.findResolvingLiteral(node1.getConclusionsAsOrFormula(),
                node2.getConclusionsAsOrFormula());
    }

    /**
     * Checks if these clauses resolve on one of the given obsolete literals. If
     * so, the obsolete clause is returned. If no clause is obsolete,
     * <code>null</code> is returned.
     * 
     * @param clause1
     * @param clause2
     * @param obsoleteLiterals
     * @return the clause that is obsolete, or <code>null</code> if none.
     */
    public static OrFormula findObsoleteClause(OrFormula clause1,
            OrFormula clause2, Set<Formula> obsoleteLiterals) {
        Formula resolvingLiteral = Util.findResolvingLiteral(clause1, clause2);

        Formula obsoleteLiteral = null;
        if (obsoleteLiterals.contains(resolvingLiteral)) {
            obsoleteLiteral = resolvingLiteral;
        } else if (obsoleteLiterals.contains(Util
                .invertLiteral(resolvingLiteral))) {
            obsoleteLiteral = Util.invertLiteral(resolvingLiteral);
        } else
            return null;

        assert (obsoleteLiteral != null);

        if (clause1.getDisjuncts().contains(obsoleteLiteral)) {
            assert (!clause2.getDisjuncts().contains(obsoleteLiteral));
            assert (!clause2.getDisjuncts().contains(
                    Util.invertLiteral(obsoleteLiteral)));
            return clause1;
        } else if (clause2.getDisjuncts().contains(obsoleteLiteral)) {
            assert (!clause1.getDisjuncts().contains(obsoleteLiteral));
            assert (!clause1.getDisjuncts().contains(
                    Util.invertLiteral(obsoleteLiteral)));
            return clause2;
        }
        assert (false); // one of the clauses *must* have the literal
        return null;
    }

    public static EqualityFormula reverseEquality(EqualityFormula formula) {
        assert (formula.getTerms().size() == 2);
        Term term1 = formula.getTerms().get(0);
        Term term2 = formula.getTerms().get(1);
        List<Term> terms = new ArrayList<Term>(2);
        terms.add(term2);
        terms.add(term1);
        try {
            return EqualityFormula.create(terms, formula.isEqual());
        } catch (IncomparableTermsException exc) {
            throw new RuntimeException(
                    "Incomparable terms during equality reversal.", exc);
        }
    }

    /**
     * Makes an ID string for the given positive literal, so that (a=b) (a!=b)
     * (b!=a) (b=a) all have the same ID.
     * 
     * @param formula
     *            a (positive!) literal
     * @return the ID string for <code>formula</code>.
     */
    public static String makeIdString(Formula formula) {

        assert (!(formula instanceof NotFormula));
        assert (Util.isLiteral(formula));
        assert (Util.isAtom(formula));

        // (a=b) (a!=b) (b!=a) (b=a) should have same IDs
        if (formula instanceof EqualityFormula) {
            List<String> terms = new ArrayList<String>();
            for (Term t : ((EqualityFormula) formula).getTerms())
                terms.add(t.toString());

            Collections.sort(terms);
            return terms.toString().replaceAll("\n", "")
                    .replaceAll("\\s{2,}", " ");
        } else
            return formula.toString().replaceAll("\n", "")
                    .replaceAll("\\s{2,}", " ");
    }

    /**
     * Determines the sign of a given literal.
     * 
     * @param literal
     *            the literal to check
     * @return the sign value of <code>literal</code>.
     */
    public static boolean getSignValue(Formula literal) {

        assert (Util.isLiteral(literal));
        boolean sign = true;

        if (literal instanceof NotFormula) {
            sign = false;
            literal = ((NotFormula) literal).getNegatedFormula();
        }

        if (literal instanceof EqualityFormula) {
            if (((EqualityFormula) literal).isEqual())
                return sign;
            else
                return !sign;
        }
        return sign;
    }

    public static final ResProof createResolutionProof(TransformedZ3Proof proof) {

        Util.resProof = new ResProof();

        Util.literalsID.clear();
        Util.resNodes.clear();

        ResNode rootNode = Util.createResolutionProofRecursive(proof);
        Util.resProof.setRoot(rootNode);

        return Util.resProof;
    }

    public static final Map<Integer, Formula> getLiteralMap() {
        return new HashMap<Integer, Formula>(Util.literalMap);
    }

    private static final ResNode createResolutionProofRecursive(
            TransformedZ3Proof proof) {

        Token proofType = proof.getProofType();

        if (proofType.equals(SExpressionConstants.ASSERTED)) {

            Formula clause = proof.getConsequent();
            assert (clause instanceof OrFormula);

            List<Literal> resClauseLits = new ArrayList<Literal>();
            // TODO: check if correct
            Set<Integer> resClausePartitions = new HashSet<Integer>();

            for (Formula literal : ((OrFormula) clause).getDisjuncts()) {

                // assign literal IDs
                Formula posLiteral = Util.makeLiteralPositive(literal);
                assert (Util.isLiteral(posLiteral));
                assert (Util.isAtom(posLiteral));

                if (posLiteral.equals(PropositionalConstant.create(false))) {
                    resClausePartitions.add(-1);
                    continue;
                }

                Integer resLiteralID = Util.literalsID.get(Util
                        .makeIdString(posLiteral));

                Set<Integer> partitions = literal.getPartitionsFromSymbols();
                if (partitions.size() == 2)
                    partitions.remove(-1);
                assert (partitions.size() == 1);
                int partition = partitions.iterator().next();

                if (resLiteralID == null) {
                    resLiteralID = Util.literalsID.size() + 1;
                    assert (!Util.literalsID.containsValue(new Integer(
                            resLiteralID)));
                    Util.literalsID.put(Util.makeIdString(posLiteral),
                            resLiteralID);
                    Util.literalMap.put(resLiteralID, posLiteral);

                    Util.resProof.putVarPart(resLiteralID, partition < 0 ? 0
                            : partition);
                }
                resClauseLits.add(Literal.create(resLiteralID,
                        Util.getSignValue(literal)));
                resClausePartitions.add(partition);
            }

            // build leaf ResNodes
            ResNode resLeafNode = Util.resNodes.get(proof.getID() + 1);
            if (resLeafNode == null) {

                if (resClausePartitions.size() == 2)
                    resClausePartitions.remove(-1);
                assert (resClausePartitions.size() == 1);

                int leafPartition = resClausePartitions.iterator().next();
                if (proof.isAxiom())
                    leafPartition = 0; // axioms should go to 0
                else if (leafPartition < 0)
                    if (proof.getAssertPartitionOfThisNode() > 0)
                        leafPartition = proof.getAssertPartitionOfThisNode();
                    else
                        leafPartition = 1; // arbitrary choice

                Clause tmpClause = new Clause(resClauseLits);
                resLeafNode = Util.resProof.addLeaf(tmpClause, leafPartition);

                Util.resNodes.put(proof.getID() + 1, resLeafNode);
            }
            return resLeafNode;

        } else if (proofType.equals(SExpressionConstants.UNIT_RESOLUTION)) {

            assert (proof.getSubProofs().size() == 2);

            ResNode resIntNode = Util.resNodes.get(proof.getID() + 1);
            if (resIntNode == null) {

                TransformedZ3Proof child1 = (TransformedZ3Proof) proof
                        .getSubProofs().get(0);
                TransformedZ3Proof child2 = (TransformedZ3Proof) proof
                        .getSubProofs().get(1);

                ResNode resNode1 = Util.createResolutionProofRecursive(child1);
                ResNode resNode2 = Util.createResolutionProofRecursive(child2);

                // build literal of resolution
                Formula posLiteral = Util.makeLiteralPositive(proof
                        .getLiteral());

                Integer literalID = Util.literalsID.get(Util
                        .makeIdString(posLiteral));

                assert (literalID != null);

                resIntNode = Util.resProof.addIntNode(null, resNode1, resNode2,
                        literalID);
                Util.resNodes.put(proof.getID() + 1, resIntNode);
            }

            return resIntNode;

        } else
            throw new RuntimeException(
                    "Resolution proof should only consist of asserted and unit-resolution elements");

    }

    /**
     * 
     * 
     * @param formula
     * @return <code>true</code> iff the given <code>formula</code> is a
     *         reflexivity (e.g.: a=a).
     */
    public static boolean isReflexivity(Formula formula) {
        // Formula tmp = formula.transformToConsequentsForm();
        if (!Util.isLiteral(formula))
            return false;
        if (!(formula instanceof DomainEq))
            return false;
        // tmp = Util.getSingleLiteral(tmp);
        // if (!(formula instanceof EqualityFormula))
        // return false;

        EqualityFormula equality = (EqualityFormula) formula;

        if (equality.getTerms().size() != 2)
            return false;

        if (!equality.isEqual())
            return false;

        Term term1 = equality.getTerms().get(0);
        Term term2 = equality.getTerms().get(1);
        assert (term1 != null);
        assert (term2 != null);
        return (term1.equals(term2));
    }

    /**
     * 
     * @param literal
     * @return <code>true</code> iff the given literal is a negated reflexivity.
     */
    public static boolean isNegatedReflexivity(Formula literal) {
        if (!Util.isNegativeLiteral(literal))
            return false;
        Formula positivLiteral = Util.makeLiteralPositive(literal);
        return Util.isReflexivity(positivLiteral);
    }

    /**
     * @param equalities
     * @return <code>true</code> iff the given chain forms a transitivity chain
     */
    public static boolean checkEqualityChain(EqualityFormula[] equalities) {
        for (EqualityFormula eq : equalities)
            assert (eq.getTerms().size() == 2);
        Term match = equalities[0].getTerms().get(1);
        for (int count = 1; count < equalities.length; count++) {
            Term current = equalities[count].getTerms().get(0);
            if (!current.equals(match))
                return false;
            match = equalities[count].getTerms().get(1);
        }
        return true;
    }

    /**
     * 
     * @param formula
     * @return <code>true</code> if this is a bad literal (having more than one
     *         partition). <code>false</code> if it is a good literal, or not a
     *         literal at all.
     */
    public static boolean isBadLiteral(Formula formula) {
        if (!Util.isLiteral(formula))
            return false;
        Set<Integer> partitions = formula.getPartitionsFromSymbols();
        partitions.remove(-1);
        if (partitions.size() > 1)
            return true;
        return false;

    }

    /**
     * 
     * @param clause
     * @return <code>true</code> if the given formula contains a bad literal
     */
    public static boolean containsBadLiteral(OrFormula clause) {
        for (Formula disjunct : clause.getDisjuncts())
            if (Util.isBadLiteral(disjunct))
                return true;
        return false;
    }

    /**
     * 
     * @param z3proof
     * @param hypothesis
     * @return if any of the subproofs of <code>z3Proof</code> is a hypothesis
     *         that has the some consequent as <code>hypothesis</code>, this
     *         subproof is returned. <code>null</code> otherwise.
     */
    public static Z3Proof findHypothesisInSubproofs(Z3Proof z3proof,
            Z3Proof hypothesis) {
        for (Z3Proof subproof : z3proof.getSubProofs()) {
            if (subproof.isHypothesis()) {
                if (subproof
                        .getConsequent()
                        .transformToConsequentsForm()
                        .equals(hypothesis.getConsequent()
                                .transformToConsequentsForm()))
                    return subproof;
            }
        }
        return null;
    }

    /**
     * Checks the given <code>node</code> for bad literals. Allows bad literals
     * only in unit clauses, and if the node deduces false. Also, allows only 2
     * subproofs.
     * 
     * @param node
     * @return <code>true</code> if the <code>node</code> passed the check
     */
    public static boolean checkResolutionNodeForBadLiterals(Z3Proof node) {
        if (node.getSubProofs().size() != 2)
            return false;

        Z3Proof sub1 = node.getSubProofs().get(0);
        Z3Proof sub2 = node.getSubProofs().get(1);

        if (!Util.containsBadLiteral((OrFormula) sub1.getConsequent())
                && !Util.containsBadLiteral((OrFormula) sub2.getConsequent()))
            return true;

        if (node.getConsequent().equals(PropositionalConstant.create(false)))
            return true;

        return false;

    }

    public static void getModusPonensNonIffChilds(Z3Proof node,
            Set<Z3Proof> result) {
        assert (result != null);
        assert (node != null);
        if (node.getConsequent() instanceof PropositionalEq) {
            for (Z3Proof child : node.getSubProofs())
                Util.getModusPonensNonIffChilds(child, result);
        } else {
            result.add(node);
        }
    }

    public static void getModusPonensIffLeafs(Z3Proof node, Set<Z3Proof> result) {
        assert (result != null);
        assert (node != null);
        if (node.getConsequent() instanceof PropositionalEq) {
            for (Z3Proof child : node.getSubProofs())
                Util.getModusPonensIffLeafs(child, result);

            if (node.getProofType().equals(SExpressionConstants.ASSERTED))
                result.add(node);
        }
    }

    public static void getModusPonensIffChildsComingFromDomainEq(Z3Proof node,
            Set<Z3Proof> result) {
        assert (result != null);
        assert (node != null);
        if (node.getConsequent() instanceof PropositionalEq) {
            if (node.getProofType().equals(SExpressionConstants.ASSERTED))
                return;
            if (node.getSubProofs().size() == 1) {
                if (node.getSubProofs().get(0).getConsequent() instanceof PropositionalEq) {
                    Util.getModusPonensIffChildsComingFromDomainEq(node
                            .getSubProofs().get(0), result);
                    return;
                }
                assert (node.getProofType()
                        .equals(SExpressionConstants.MONOTONICITY));
                Z3Proof child = node.getSubProofs().get(0);
                Formula childConsequent = child.getConsequent();
                assert (Util.isLiteral(childConsequent));
                childConsequent = Util.getSingleLiteral(childConsequent);
                assert (Util.isAtom(childConsequent));
                if (!(childConsequent instanceof DomainEq))
                    assert (false);
                result.add(node);
                return;
            }
            if (node.getSubProofs().size() == 2
                    && node.getProofType().equals(
                            SExpressionConstants.MONOTONICITY)) {
                assert (node.getProofType()
                        .equals(SExpressionConstants.MONOTONICITY));
                Z3Proof child1 = node.getSubProofs().get(0);
                Z3Proof child2 = node.getSubProofs().get(1);
                Formula childConsequent1 = child1.getConsequent();
                assert (Util.isLiteral(childConsequent1));
                childConsequent1 = Util.getSingleLiteral(childConsequent1);
                assert (Util.isAtom(childConsequent1));
                if (!(childConsequent1 instanceof DomainEq))
                    assert (false);
                Formula childConsequent2 = child2.getConsequent();
                assert (Util.isLiteral(childConsequent2));
                childConsequent2 = Util.getSingleLiteral(childConsequent2);
                assert (Util.isAtom(childConsequent2));
                if (!(childConsequent2 instanceof DomainEq))
                    assert (false);
                result.add(node);
                return;
            }
            for (Z3Proof child : node.getSubProofs())
                Util.getModusPonensIffChildsComingFromDomainEq(child, result);
        } else {
            assert (false); // Unexpected exit path from modus ponens rule
        }
    }

    /**
     * Returns the partition of the consequent of this proof. Fails with
     * assertion error, if there are local symbols from multiple partitions.
     * 
     * @param transformedZ3Proof
     * @return The partition of the symbols of the consequent of the given
     *         proof, or <code>1</code> if there are only global symbols
     */
    public static int getSinglePartitionOfProof(
            TransformedZ3Proof transformedZ3Proof) {
        Set<Integer> partitions = transformedZ3Proof.getConsequent()
                .getPartitionsFromSymbols();
        partitions.remove(-1);
        if (partitions.size() == 0)
            return 1; // arbitrary choice
        assert (partitions.size() == 1);
        return partitions.iterator().next();
    }

    /**
     * @param badLiteral
     * @return
     */
    public static String formulaToStringWithoutNewlines(Formula formula) {
        return formula.toString().replaceAll("\\s{2,}", " ").replace("\n", "");
    }

    /**
     * Compares to clauses for (logical) equality. I.e., the order or literals
     * is immaterial.
     * 
     * @param clause1
     * @param clause2
     * @return <code>true</code> if both given formulas are clauses and they are
     *         logically equivalent.
     */
    public static boolean equalClauses(Formula clause1, Formula clause2) {
        if (!(clause1 instanceof OrFormula))
            return false;
        if (!(clause2 instanceof OrFormula))
            return false;

        if (clause1.equals(clause2))
            return true;

        return (new HashSet<Formula>(((OrFormula) clause1).getDisjuncts()))
                .equals((new HashSet<Formula>(((OrFormula) clause2)
                        .getDisjuncts())));
    }

    /**
     * Constructs a reflexivity formula over the given <code>term</code>.
     * 
     * @param term
     * @return a reflexivity formula over the given <code>term</code>.
     */
    public static DomainEq createReflexivity(DomainTerm term) {
        List<DomainTerm> terms = new ArrayList<DomainTerm>();
        terms.add(term);
        terms.add(term);
        DomainEq result = DomainEq.create(terms, true);
        return result;
    }

    /**
     * Tests whether each collection in the given collection of collections has
     * exactly one element.
     * 
     * @param collectionOfCollections
     *            the collection of collections to test
     * @return <code>true</code> iff all collections in the
     *         <code>collectionOfCollections</code> have exactly one element.
     */
    public static boolean allElementsSizeOne(
            Collection<? extends Collection<?>> collectionOfCollections) {
        for (Collection<?> collection : collectionOfCollections) {
            if (collection.size() != 1)
                return false;
        }
        return true;
    }

    /**
     * Removes (negative) reflexive literals. They are false anyway. This
     * methode modifies the given list.
     * 
     * @param literals
     *            the list of literals (will be modified)
     */
    public static void removeReflexiveLiterals(List<Formula> literals) {
        Set<Formula> literalsToRemove = new HashSet<Formula>();
        for (Formula literal : literals) {
            assert (Util.isLiteral(literal));
            if (Util.isNegativeLiteral(literal)) {
                Formula positiveLiteral = Util.makeLiteralPositive(literal);
                if (Util.isReflexivity(positiveLiteral))
                    literalsToRemove.add(literal);
            }
        }
        literals.removeAll(literalsToRemove);
    }

    /**
     * Prints the given line to <code>System.out</code> using
     * <code>println</code>. The current date/time is prepended.
     * 
     * @param line
     *            the line to print
     */
    public static synchronized void printToSystemOutWithWallClockTimePrefix(
            String line) {
        DateFormat dateFormat = DateFormat.getDateTimeInstance(
                DateFormat.MEDIUM, DateFormat.MEDIUM);
        String dateTimeString = dateFormat.format(new Date());
        System.out.println("[" + dateTimeString + "] " + line);
    }

    public static synchronized void printMemoryInformation() {
        System.out
                .println("--------------------------------------------------------------------------------");
        System.out.println("MEMORY INFORMATION:");
        System.out.println("Total Memory: "
                + Util.byteAmountFormatter.format(Runtime.getRuntime()
                        .totalMemory()));
        System.out.println("Free Memory : "
                + Util.byteAmountFormatter.format(Runtime.getRuntime()
                        .freeMemory()));
        System.out.println("Max. Memory : "
                + Util.byteAmountFormatter.format(Runtime.getRuntime()
                        .maxMemory()));
        System.out
                .println("--------------------------------------------------------------------------------");
    }

    /**
     * 
     * @param term
     * @return <code>true</code> iff the given term is a global term.
     */
    public static boolean isGlobal(Term term) {
        Set<Integer> partitions = term.getPartitionsFromSymbols();
        if (partitions.size() > 1)
            return false;
        partitions.remove(-1);
        return partitions.isEmpty();
    }

    /**
     * @param formula
     * @return <code>true</code> iff the given formula contains only global
     *         symbols.
     */
    public static boolean isGlobal(Formula formula) {
        Set<Integer> partitions = formula.getPartitionsFromSymbols();
        partitions.remove(-1);
        return partitions.isEmpty();
    }

    /**
     * @param usedLiterals
     * @return
     */
    public static List<Formula> invertAllLiterals(Collection<Formula> literals) {
        List<Formula> result = new ArrayList<Formula>(literals.size());
        for (Formula literal : literals) {
            result.add(Util.invertLiteral(literal));
        }
        return result;
    }

    /**
     * Reverses the order of the terms in the given <code>literal</code>.
     * <code>literal</code> must be an <code>EqualityFormula</code> with exactly
     * two terms. A negated literal is also allowed. If the literal is not an
     * equality literal, it is returned unchanged.
     * 
     * @param literal
     * @return the literal with terms in reversed order.
     */
    public static Formula reverseTermsInLiteral(Formula literal) {
        assert (Util.isLiteral(literal));
        if (!(Util.makeLiteralPositive(literal) instanceof EqualityFormula))
            return literal;
        EqualityFormula eq = (EqualityFormula) Util
                .makeLiteralPositive(literal);
        assert (eq.getTerms().size() == 2);
        List<Term> terms = new ArrayList<Term>(2);
        terms.add(eq.getTerms().get(1));
        terms.add(eq.getTerms().get(0));
        EqualityFormula newEq;
        try {
            newEq = EqualityFormula.create(terms, true);
        } catch (IncomparableTermsException exc) {
            throw new RuntimeException(
                    "Unexpected exception while trying to reverse terms in literal.");
        }
        if (Util.getSignValue(literal))
            return newEq;
        else
            return NotFormula.create(newEq);
    }

    /**
     * Counts how many negative literals are contained in the given collection.
     * Positive literals and non-literals are not counted.
     * 
     * @param literals
     * @return the number of negative literals in the given Collection.
     */
    public static int countNegativeLiterals(
            Collection<? extends Formula> literals) {
        int count = 0;
        for (Formula literal : literals) {
            if (Util.isNegativeLiteral(literal))
                count++;
        }
        return count;
    }

    /**
     * Counts how many positive literals are contained in the given collection.
     * Negative literals and non-literals are not counted.
     * 
     * @param literals
     * @return the number of positive literals in the given Collection.
     */
    public static int countPositiveLiterals(
            Collection<? extends Formula> literals) {
        int count = 0;
        for (Formula literal : literals) {
            if (Util.isAtom(literal))
                count++;
        }
        return count;
    }

    /**
     * Returns the first positive literal found in the given collection, or
     * <code>null</code> if no such literal exists.
     * 
     * @param literals
     * @return the first positive literal found in the given collection, or
     *         <code>null</code> if no such literal exists.
     */
    public static Formula findPositiveLiteral(
            Collection<? extends Formula> literals) {
        for (Formula literal : literals) {
            if (Util.isAtom(literal))
                return literal;
        }
        return null;
    }

    /**
     * Returns the implied literal of this collection. Unlike
     * <code>findPositiveLiteral</code>, this checks whether there is only one
     * positive (implied) literal. This also checks that all other formulas
     * actually are literals.
     * 
     * @param literals
     * @return the (unique) implied literal of this collection or
     *         <code>null</code> if no such (unique) literal exists
     */
    public static Formula getImpliedLiteral(
            Collection<? extends Formula> literals) {
        Formula result = null;
        for (Formula literal : literals) {
            if (!Util.isLiteral(literal))
                return null;
            if (Util.isAtom(literal)) {
                if (result != null)
                    return null;
                else
                    result = literal;
            }
        }
        return result;
    }

    /**
     * Searches the given collection of <code>literals</code> for a predicate
     * instance of the same predicate as <code>predicateInstance</code> but in
     * inverse (i.e., negative) polarity. The first matching predicate instance
     * found is returned. There is no check done whether there would be more.
     * Note that the returned formula will not be the negative literal, but just
     * the predicate inside the <code>NotFormula</code>.
     * 
     * @param predicateInstance
     * @param literals
     * @return the inverse predicate instance, or <code>null</code> if not found
     */
    public static UninterpretedPredicateInstance findInversePredicateLiteral(
            UninterpretedPredicateInstance predicateInstance,
            Collection<? extends Formula> literals) {
        assert (predicateInstance != null);
        assert (literals != null);
        UninterpretedFunction predicate = predicateInstance.getFunction();
        for (Formula literal : literals) {
            if (Util.isNegativeLiteral(literal)) {
                Formula positiveLiteral = Util.makeLiteralPositive(literal);
                if (positiveLiteral instanceof UninterpretedPredicateInstance) {
                    if (((UninterpretedPredicateInstance) positiveLiteral)
                            .getFunction().equals(predicate)) {
                        return (UninterpretedPredicateInstance) positiveLiteral;
                    }
                }
            }
        }
        return null;
    }

    /**
     * @param literal1
     * @param literal2
     * @return
     */
    public static boolean areReversedLiterals(Formula literal1, Formula literal2) {
        assert (literal1 != null);
        assert (literal2 != null);
        assert (Util.isLiteral(literal1));
        assert (Util.isLiteral(literal2));
        Formula positiveLiteral1 = Util.makeLiteralPositive(literal1);
        Formula positiveLiteral2 = Util.makeLiteralPositive(literal2);
        if (!(positiveLiteral1 instanceof EqualityFormula))
            return false;
        if (!(positiveLiteral2 instanceof EqualityFormula))
            return false;
        EqualityFormula equality1 = (EqualityFormula) positiveLiteral1;
        EqualityFormula equality2 = (EqualityFormula) positiveLiteral2;
        assert (equality1.getTerms().size() == 2);
        assert (equality2.getTerms().size() == 2);
        if (!equality1.getTerms().get(0).equals(equality2.getTerms().get(1)))
            return false;
        if (!equality1.getTerms().get(1).equals(equality2.getTerms().get(0)))
            return false;
        return true;
    }

    /**
     * 
     * @param conclusions1
     *            Literals of first subproof
     * @param conclusions2
     *            Literals of second subproof
     * @return conclusions for the resolution of <code>literals1</code> and
     *         <code>literals2</code>.
     */
    public static List<Formula> findConclusionsOfResolution(
            Collection<? extends Formula> conclusions1,
            Collection<? extends Formula> conclusions2) {

        List<Formula> result = new ArrayList<Formula>(conclusions1.size()
                + conclusions2.size());

        for (Formula literal : conclusions1) {
            if (!result.contains(literal)) {
                if (!conclusions2.contains(Util.invertLiteral(literal))) {
                    result.add(literal);
                }
            }
        }

        for (Formula literal : conclusions2) {
            if (!result.contains(literal)) {
                if (!conclusions1.contains(Util.invertLiteral(literal))) {
                    result.add(literal);
                }
            }
        }

        return result;

    }

    /**
     * 
     * @param literal
     * @param literalIds
     * @param partitions
     *            mapping of literal IDs to partitions (0 for global) will be
     *            stored here.
     * @param literalMap
     *            map from literal IDs (Integers) to <code>Formula</code>
     *            objects. (will be updated here)
     * @return the id of the given literal in the given map, or a fresh id
     *         (which is stored to the map)
     */
    public static int getLiteralId(Formula literal,
            Map<String, Integer> literalIds, Map<Integer, Integer> partitions,
            Map<Integer, Formula> literalMap) {
        assert (Util.isLiteral(literal));
        Formula atom = Util.makeLiteralPositive(literal);
        String idString = Util.makeIdString(atom);
        Integer id = literalIds.get(idString);
        if (id == null) {
            id = literalIds.size() + 1;
            assert (!literalIds.containsKey(id));
            literalIds.put(idString, id);
            Set<Integer> literalPartitions = literal.getPartitionsFromSymbols();
            literalPartitions.remove(-1);
            assert (literalPartitions.size() <= 1);
            int literalPartition = literalPartitions.isEmpty() ? 0
                    : literalPartitions.iterator().next();
            partitions.put(id, literalPartition);
        }
        literalMap.put(id, atom);
        return id;
    }

    /**
     * Dumps the given metadata to files
     * 
     * @param filePrefix
     * @param literalIds
     * @param literalMap
     * @param partitions
     * @param leafPartitions
     * @throws IOException
     */
    public static void dumpMetaData(String filePrefix,
            Map<String, Integer> literalIds, Map<Integer, Formula> literalMap,
            Map<Integer, Integer> partitions,
            Map<ImmutableSet<Integer>, Integer> leafPartitions)
            throws IOException {

        Util.printToSystemOutWithWallClockTimePrefix("Starting to dump metadata to files "
                + filePrefix + ".* ...");
        Util.dumpLiteralMap(filePrefix + ".literalMap", literalMap);
        Util.dumpPartitions(filePrefix + ".partitions", partitions);
        Util.dumpLeafPartitions(filePrefix + ".leafPartitions", leafPartitions);
        Util.printToSystemOutWithWallClockTimePrefix("Done.");
    }

    /**
     * Dumps literalMap to given file.
     * 
     * @param fileName
     * @param literalMap
     * @throws IOException
     */
    public static void dumpLiteralMap(String fileName,
            Map<Integer, Formula> literalIds) throws IOException {
        Writer fileStream = new FileWriter(fileName);
        BufferedWriter writer = new BufferedWriter(fileStream);
        for (Integer id : literalIds.keySet()) {
            Formula formula = literalIds.get(id);
            assert (formula != null);
            writer.write("(");
            writer.write(id.toString());
            writer.write(" ");
            writer.write(formula.toSmtlibV2().toString());
            writer.write(")\n");
        }
        writer.close();
    }

    /**
     * 
     * @param fileName
     * @param parser
     *            a parser pre-initialized with the correct set of variable and
     *            function names.
     * @return the literal map loaded from the given file
     * @throws ParseError
     * @throws IOException
     * @throws FileNotFoundException
     */
    public static Map<Integer, Formula> loadLiteralMap(String fileName,
            LogicParser parser) throws ParseError, FileNotFoundException,
            IOException {
        Map<Integer, Formula> result = new HashMap<Integer, Formula>();

        SExpParser sexpParser = new SExpParser(new File(fileName));
        sexpParser.parse();
        SExpression rootExpr = sexpParser.getRootExpr();
        sexpParser = null; // GC

        for (SExpression expr : rootExpr.getChildren()) {
            if (expr.getChildren().size() != 2)
                throw new ParseError("Illegal number of child expressions");
            if (!(expr.getChildren().get(0) instanceof Token))
                throw new ParseError("First child not a token");
            int literal = Integer
                    .parseInt(expr.getChildren().get(0).toString());
            Formula formula = parser
                    .parseFormulaBody(expr.getChildren().get(1));
            result.put(literal, formula);
        }

        return result;
    }

    /**
     * Dumps the given leafPartitions to the given file.
     * 
     * @param fileName
     * @param leafPartitions
     * @throws IOException
     */
    public static void dumpLeafPartitions(String fileName,
            Map<ImmutableSet<Integer>, Integer> leafPartitions)
            throws IOException {
        Writer fileStream = new FileWriter(fileName);
        BufferedWriter writer = new BufferedWriter(fileStream);
        for (ImmutableSet<Integer> clause : leafPartitions.keySet()) {
            Integer partition = leafPartitions.get(clause);
            assert (partition != null);
            writer.write(partition.toString());
            writer.write(" : ");
            for (Integer integer : clause) {
                writer.write(integer.toString());
                writer.write(" ");
            }
            writer.write("\n");
        }
        writer.close();
    }

    /**
     * 
     * @param fileName
     * @return leaf partitions loaded from the given file.
     * @throws IOException
     */
    public static Map<ImmutableSet<Integer>, Integer> loadLeafPartitions(
            String fileName) throws IOException {
        BufferedReader reader = new BufferedReader(new FileReader(fileName));
        Map<ImmutableSet<Integer>, Integer> result = new HashMap<ImmutableSet<Integer>, Integer>();

        String line;
        while ((line = reader.readLine()) != null) {
            String[] tokens = line.split(" ");
            assert (tokens.length >= 3);
            assert (tokens[1].equals(":"));
            int partition = Integer.parseInt(tokens[0]);
            Set<Integer> clause = new TreeSet<Integer>();
            for (int count = 2; count < tokens.length; count++) {
                clause.add(Integer.parseInt(tokens[count]));
            }
            result.put(ImmutableSet.create(clause), partition);
        }

        reader.close();
        return result;
    }

    /**
     * Dumps the given partitions to the given file.
     * 
     * @param fileName
     * @param partitions
     * @throws IOException
     */
    public static void dumpPartitions(String fileName,
            Map<Integer, Integer> partitions) throws IOException {
        Writer fileStream = new FileWriter(fileName);
        BufferedWriter writer = new BufferedWriter(fileStream);
        for (Integer lit : partitions.keySet()) {
            Integer partition = partitions.get(lit);
            assert (partition != null);
            writer.write(lit.toString());
            writer.write(" ");
            writer.write(partition.toString());
            writer.write("\n");
        }
        writer.close();
    }

    /**
     * 
     * @param fileName
     * @return partitions loaded from the given file.
     * @throws IOException
     */
    public static Map<Integer, Integer> loadPartitions(String fileName)
            throws IOException {
        BufferedReader reader = new BufferedReader(new FileReader(fileName));
        Map<Integer, Integer> result = new HashMap<Integer, Integer>();

        String line;
        while ((line = reader.readLine()) != null) {
            String[] tokens = line.split(" ");
            assert (tokens.length == 2);
            int lit = Integer.parseInt(tokens[0]);
            int partition = Integer.parseInt(tokens[1]);
            result.put(lit, partition);
        }

        reader.close();
        return result;
    }

    /**
     * Writes all declarations required for <code>formula</code> to
     * <code>writer.</code>
     * 
     * @param formula
     * @param writer
     * @throws IOException
     */
    public static void writeDeclarations(Formula formula, BufferedWriter writer)
            throws IOException {
        Set<SMTLibObject> done = new HashSet<SMTLibObject>();
        Set<PropositionalVariable> propVars = new HashSet<PropositionalVariable>();
        formula.getPropositionalVariables(propVars, done);
        done.clear();
        for (PropositionalVariable propVar : propVars) {
            writer.write("(" + SExpressionConstants.DECLARE_FUN.toString()
                    + " " + propVar.getVarName() + " () "
                    + SExpressionConstants.BOOL_TYPE.toString() + " )\n");
        }

        Set<DomainVariable> domainVars = new HashSet<DomainVariable>();
        formula.getDomainVariables(domainVars, done);
        done.clear();
        for (DomainVariable domainVar : domainVars) {
            writer.write("(" + SExpressionConstants.DECLARE_FUN.toString()
                    + " " + domainVar.getVarName() + " () "
                    + SExpressionConstants.VALUE_TYPE.toString() + " )\n");
        }

        Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();
        formula.getArrayVariables(arrayVars, done);
        done.clear();
        for (ArrayVariable arrayVar : arrayVars) {
            writer.write("(" + SExpressionConstants.DECLARE_FUN.toString()
                    + " " + arrayVar.getVarName() + " () "
                    + SExpressionConstants.ARRAY_TYPE.toString() + " )\n");
        }

        Set<UninterpretedFunction> uninterpretedFunctions = new HashSet<UninterpretedFunction>();
        formula.getUninterpretedFunctions(uninterpretedFunctions, done);
        done.clear();
        for (UninterpretedFunction function : uninterpretedFunctions) {
            StringBuilder params = new StringBuilder();
            final int numParams = function.getNumParams();
            for (int count = 0; count < numParams; count++) {
                params.append(SExpressionConstants.VALUE_TYPE.toString());
                if (count != numParams - 1)
                    params.append(" ");
            }
            writer.write("(" + SExpressionConstants.DECLARE_FUN.toString()
                    + " " + function.getName().toString() + " ("
                    + params.toString() + ") " + function.getType() + " )\n");
        }

    }

    /**
     * @param interpolant
     * @param partitionFormulas
     * @return <code>true</code> if the given interpolant is a partial
     *         interpolant with respect to the partition formulas.
     */
    public static boolean checkInterpolant(Formula interpolant,
            Map<Integer, Formula> partitionFormulas) {
        return Util.checkPartialInterpolant(interpolant, null,
                partitionFormulas);
    }

    /**
     * @param interpolant
     * @param clause
     * @param partitionFormulas
     * @return <code>true</code> if the given interpolant is a partial
     *         interpolant with respect to the partition formulas and the given
     *         clause.
     */
    public static boolean checkPartialInterpolant(Formula interpolant,
            Formula clause, Map<Integer, Formula> partitionFormulas) {

        List<Formula> conjunctsA = new ArrayList<Formula>(
                partitionFormulas.size() / 2 + 1);
        List<Formula> conjunctsB = new ArrayList<Formula>(
                partitionFormulas.size() / 2 + 1);

        for (int num : partitionFormulas.keySet()) {
            Formula partition = partitionFormulas.get(num);
            assert (partition != null);
            if ((num - 1) % 2 == 0)
                conjunctsA.add(partition);
            else
                conjunctsB.add(partition);
        }

        AndFormula partitionsA = AndFormula.generate(conjunctsA);
        AndFormula partitionsB = AndFormula.generate(conjunctsB);

        Formula impliedByA = interpolant;
        Formula impliedByB = NotFormula.create(interpolant);

        if (clause != null) {
            List<Formula> disjuncts = new ArrayList<Formula>(2);
            disjuncts.add(impliedByA);
            disjuncts.add(clause);
            impliedByA = OrFormula.generate(disjuncts);

            List<Formula> disjuncts2 = new ArrayList<Formula>(2);
            disjuncts2.add(impliedByB);
            disjuncts2.add(clause);
            impliedByB = OrFormula.generate(disjuncts2);
        }

        if (!Util.checkFormulaImplication(partitionsA, impliedByA))
            return false;

        if (!Util.checkFormulaImplication(partitionsB, impliedByB))
            return false;

        Set<SMTLibObject> symbolsA = new HashSet<SMTLibObject>();
        Set<DomainVariable> domainVarsA = new HashSet<DomainVariable>();
        partitionsA
                .getDomainVariables(domainVarsA, new HashSet<SMTLibObject>());
        symbolsA.addAll(domainVarsA);
        Set<PropositionalVariable> propVarsA = new HashSet<PropositionalVariable>();
        partitionsA.getPropositionalVariables(propVarsA,
                new HashSet<SMTLibObject>());
        symbolsA.addAll(propVarsA);
        Set<ArrayVariable> arrayVarsA = new HashSet<ArrayVariable>();
        partitionsA.getArrayVariables(arrayVarsA, new HashSet<SMTLibObject>());
        symbolsA.addAll(arrayVarsA);
        Set<UninterpretedFunction> ufsA = new HashSet<UninterpretedFunction>();
        partitionsA
                .getUninterpretedFunctions(ufsA, new HashSet<SMTLibObject>());
        symbolsA.addAll(ufsA);

        Set<SMTLibObject> symbolsB = new HashSet<SMTLibObject>();
        Set<DomainVariable> domainVarsB = new HashSet<DomainVariable>();
        partitionsB
                .getDomainVariables(domainVarsB, new HashSet<SMTLibObject>());
        symbolsB.addAll(domainVarsB);
        Set<PropositionalVariable> propVarsB = new HashSet<PropositionalVariable>();
        partitionsB.getPropositionalVariables(propVarsB,
                new HashSet<SMTLibObject>());
        symbolsB.addAll(propVarsB);
        Set<ArrayVariable> arrayVarsB = new HashSet<ArrayVariable>();
        partitionsB.getArrayVariables(arrayVarsB, new HashSet<SMTLibObject>());
        symbolsB.addAll(arrayVarsB);
        Set<UninterpretedFunction> ufsB = new HashSet<UninterpretedFunction>();
        partitionsB
                .getUninterpretedFunctions(ufsB, new HashSet<SMTLibObject>());
        symbolsB.addAll(ufsB);

        Set<SMTLibObject> symbolsI = new HashSet<SMTLibObject>();
        Set<DomainVariable> domainVarsI = new HashSet<DomainVariable>();
        interpolant
                .getDomainVariables(domainVarsI, new HashSet<SMTLibObject>());
        symbolsI.addAll(domainVarsI);
        Set<PropositionalVariable> propVarsI = new HashSet<PropositionalVariable>();
        interpolant.getPropositionalVariables(propVarsI,
                new HashSet<SMTLibObject>());
        symbolsI.addAll(propVarsI);
        Set<ArrayVariable> arrayVarsI = new HashSet<ArrayVariable>();
        interpolant.getArrayVariables(arrayVarsI, new HashSet<SMTLibObject>());
        symbolsI.addAll(arrayVarsI);
        Set<UninterpretedFunction> ufsI = new HashSet<UninterpretedFunction>();
        interpolant
                .getUninterpretedFunctions(ufsI, new HashSet<SMTLibObject>());
        symbolsI.addAll(ufsI);

        Set<SMTLibObject> symbolsC = new HashSet<SMTLibObject>();
        if (clause != null) {
            Set<DomainVariable> domainVarsC = new HashSet<DomainVariable>();
            clause.getDomainVariables(domainVarsC, new HashSet<SMTLibObject>());
            symbolsC.addAll(domainVarsC);
            Set<PropositionalVariable> propVarsC = new HashSet<PropositionalVariable>();
            clause.getPropositionalVariables(propVarsC,
                    new HashSet<SMTLibObject>());
            symbolsC.addAll(propVarsC);
            Set<ArrayVariable> arrayVarsC = new HashSet<ArrayVariable>();
            clause.getArrayVariables(arrayVarsC, new HashSet<SMTLibObject>());
            symbolsC.addAll(arrayVarsC);
            Set<UninterpretedFunction> ufsC = new HashSet<UninterpretedFunction>();
            clause.getUninterpretedFunctions(ufsC, new HashSet<SMTLibObject>());
            symbolsC.addAll(ufsC);
        }

        Set<Object> globalSymbols = new HashSet<Object>();
        for (Object symbol : symbolsA) {
            if (symbolsB.contains(symbol))
                globalSymbols.add(symbol);
        }

        for (Object symbol : symbolsI) {
            if (!globalSymbols.contains(symbol) && !symbolsC.contains(symbol))
                return false;
        }

        return true;
    }

    /**
     * 
     * @param interpolant
     * @param theoryLemma
     * @return <code>true</code> iff the given <code>interpolant</code> is a
     *         valid interpolant for <code>theoryLemma</code>.
     */
    public static boolean checkTheoryLemmaInterpolant(Formula interpolant,
            OrFormula theoryLemma) {
        List<Formula> literals = theoryLemma.getDisjuncts();
        List<Formula> literalsA = new ArrayList<Formula>(literals.size());
        List<Formula> literalsB = new ArrayList<Formula>(literals.size());

        for (Formula literal : literals) {
            assert (Util.isLiteral(literal));
            Set<Integer> partitions = literal.getPartitionsFromSymbols();
            partitions.remove(-1);
            literal = Util.invertLiteral(literal);
            if (partitions.isEmpty()) {
                literalsA.add(literal);
                literalsB.add(literal);
            } else {
                assert (partitions.size() == 1);
                int partition = partitions.iterator().next();
                if ((partition - 1) % 2 == 0)
                    literalsA.add(literal);
                else
                    literalsB.add(literal);
            }
        }

        AndFormula cubeA = AndFormula.generate(literalsA);
        AndFormula cubeB = AndFormula.generate(literalsB);

        if (!Util.checkFormulaImplication(cubeA, interpolant))
            return false;

        if (!Util
                .checkFormulaImplication(cubeB, NotFormula.create(interpolant)))
            return false;

        if (!Util.isGlobal(interpolant))
            return false;

        return true;
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
        Set<SMTLibObject> done = new HashSet<SMTLibObject>();

        Set<DomainVariable> domainVars1 = new HashSet<DomainVariable>();
        formula1.getDomainVariables(domainVars1, done);
        done.clear();
        Set<PropositionalVariable> propVars1 = new HashSet<PropositionalVariable>();
        formula1.getPropositionalVariables(propVars1, done);
        done.clear();
        Set<UninterpretedFunction> uif1 = new HashSet<UninterpretedFunction>();
        formula1.getUninterpretedFunctions(uif1, done);
        done.clear();

        Set<DomainVariable> domainVars2 = new HashSet<DomainVariable>();
        formula2.getDomainVariables(domainVars2, done);
        done.clear();
        Set<PropositionalVariable> propVars2 = new HashSet<PropositionalVariable>();
        formula2.getPropositionalVariables(propVars2, done);
        done.clear();
        Set<UninterpretedFunction> uif2 = new HashSet<UninterpretedFunction>();
        formula2.getUninterpretedFunctions(uif2, done);
        done.clear();

        // Vars can be different when one formula contains redundant vars (such
        // as (x and not x)).
        //
        // if (!domainVars1.equals(domainVars2))
        // return false;
        // if (!propVars1.equals(propVars2))
        // return false;
        // if (!uif1.equals(uif2))
        // return false;

        if (!Util.checkFormulaImplication(formula1, formula2))
            return false;
        if (!Util.checkFormulaImplication(formula2, formula1))
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
        conjuncts.add(NotFormula.create(formula2));
        Formula formulaToCheck = AndFormula.generate(conjuncts);

        SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type,
                SuraqOptions.getZ3Path());
        // DebugHelper.getInstance().stringtoFile(smtstr,
        // "debug-tseitin-check.txt");
        // System.out.print('.');
        z3.solve(formulaToCheck);

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
     * 
     * @param formula
     * @return <code>true</code> iff the given formula is UNSAT.
     */
    public static boolean checkUnsat(Formula formula) {
        SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type,
                SuraqOptions.getZ3Path());

        z3.solve(formula);

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
     * @param aigNodes
     * @param done
     * @return
     */
    public static int nextFreePositiveAigLiteral(
            TreeMap<Integer, Integer[]> aigNodes, Map<Formula, Integer> done) {
        return aigNodes.isEmpty() ? 2 + done.size() * 2 : ((aigNodes
                .descendingKeySet().iterator().next() + 2) / 2) * 2;
    }

    /**
     * Writes the given formula to the given writer, using let expressions.
     * 
     * @param formula
     * @param writer
     * @throws IOException
     */
    public static void writeFormulaUsingLetExpressions(Formula formula,
            Writer writer) throws IOException {

        BigInteger size = formula
                .size(true, new HashMap<Formula, BigInteger>());
        if (size.compareTo(new BigInteger("100")) < 0) {
            Util.printToSystemOutWithWallClockTimePrefix("Writing small formula without let expressions. (Size: "
                    + size.toString() + ")");
            formula.writeTo(writer);
            return;
        }

        Map<Formula, Set<Formula>> parents = new HashMap<Formula, Set<Formula>>();
        formula.computeParents(parents, new HashSet<Formula>());

        Set<Formula> pseudoLeaves = new HashSet<Formula>();
        formula.getLiterals(pseudoLeaves, new HashSet<Formula>());
        pseudoLeaves.add(PropositionalConstant.create(true));
        pseudoLeaves.add(PropositionalConstant.create(false));

        Set<Term> terms = new HashSet<Term>();
        formula.getTerms(terms, new HashSet<Formula>());

        int idCounter = 0;

        // Start outermost let-expression (the one defining terms).
        writer.write("(let (\n");
        Map<SMTLibObject, String> letDefinitions = new HashMap<SMTLibObject, String>();
        for (Term term : terms) {
            String id = "et!" + Integer.toString(idCounter++);
            letDefinitions.put(term, id);
            writer.write("(");
            writer.write(id);
            writer.write(" ");
            term.writeTo(writer);
            writer.write(")\n");
        }
        writer.write(")\n("); // opens the formula part of the outermost let
                              // expression.

        Set<Formula> currentFormulasToDefine = new HashSet<Formula>(
                pseudoLeaves);

        int letLevels = 0;
        while (!currentFormulasToDefine.isEmpty()) {
            // start the current let expression
            letLevels++;
            writer.write("let (\n");
            for (Formula currentFormula : currentFormulasToDefine) {
                writer.write("(");
                String id = "ef!" + Integer.toString(idCounter++);
                writer.write(id);
                writer.write(" ");
                currentFormula.writeTo(writer, letDefinitions);
                writer.write(")\n");
                letDefinitions.put(currentFormula, id);
                pseudoLeaves.add(currentFormula);
            }

            // Compute the next formulas to define
            Set<Formula> nextFormulasToDefine = new HashSet<Formula>();
            for (Formula currentFormula : currentFormulasToDefine) {
                Set<Formula> currentParents = parents.get(currentFormula);
                if (currentParents == null
                        && !(currentFormula instanceof PropositionalConstant)) {
                    assert (currentFormula == formula);
                    assert (currentFormulasToDefine.size() == 1 || (currentFormulasToDefine
                            .size() <= 3
                            && currentFormulasToDefine
                                    .contains(PropositionalConstant
                                            .create(true)) && currentFormulasToDefine
                                .contains(PropositionalConstant.create(false))));
                    assert (nextFormulasToDefine.isEmpty());
                    assert (letDefinitions.get(formula) != null);
                    currentFormulasToDefine.clear();
                    break;
                }
                if (currentParents != null) {
                    for (Formula parent : currentParents) {
                        if (parent.dependsOnlyOn(pseudoLeaves))
                            nextFormulasToDefine.add(parent);
                    }
                } else
                    assert (currentFormula instanceof PropositionalConstant);
            }
            if (!nextFormulasToDefine.isEmpty()) {
                // open the formula part of the current let expression
                writer.write(")\n(");
                currentFormulasToDefine = nextFormulasToDefine;
            }
        }
        writer.write(")"); // Close definitions of innermost let
        String rootId = letDefinitions.get(formula);
        assert (rootId != null);
        writer.write(rootId);

        // Close parentheses for let expressions and their formulas
        StringBuilder builder = new StringBuilder();
        for (int count = 0; count < letLevels; count++)
            builder.append(")");
        writer.write(builder.toString());

        // Close outermost let-expression (the one defining terms)
        writer.write("\n)");
        writer.flush();
    }

    /**
     * Writes the given formula to a file with the given name.
     * 
     * @param formula
     * @param name
     * @param useLet
     *            whether or not to use let-expressions
     * @param writeDeclarations
     */
    public static void writeFormulaToFile(Formula formula, String name,
            boolean useLet, boolean writeDeclarations) {
        try {
            File file = new File(name);
            FileWriter fwriter = new FileWriter(file);
            BufferedWriter writer = new BufferedWriter(fwriter);
            if (writeDeclarations)
                Util.writeDeclarations(formula, writer);
            if (useLet)
                Util.writeFormulaUsingLetExpressions(formula, writer);
            else
                formula.writeTo(writer);
            writer.close();
            fwriter.close();
        } catch (IOException exc) {
            Util.printToSystemOutWithWallClockTimePrefix("Error writing formula to file.");
            exc.printStackTrace();
        }
    }
}
