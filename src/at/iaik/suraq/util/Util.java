/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.IncomparableTermsException;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.proof.AnnotatedProofNode;
import at.iaik.suraq.resProof.Lit;
import at.iaik.suraq.resProof.ResNode;
import at.iaik.suraq.resProof.ResProof;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.TransformedZ3Proof;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.FormulaTerm;
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

/**
 * 
 * Collection of (static) utility methods.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class Util {

    private static Map<String, Integer> literalsID = new HashMap<String, Integer>();
    private static Map<Integer, ResNode> resNodes = new HashMap<Integer, ResNode>();
    private static ResProof resProof;
    private static Map<Integer, Formula> literalMap = new HashMap<Integer, Formula>();

    /**
     * Counts the number of Tseitin vars that have been introduced so far. This
     * makes sure they all get a unique name.
     */
    private static int tseitinVarCounter = 0;

    /**
     * 
     * @param partition
     *            the assert partition with which the variable will be
     *            associated.
     * @return a Tseitin variable with a name that has not been returned before.
     */
    public static PropositionalVariable freshTseitinVar(int partition) {
        return new PropositionalVariable("ts!" + Util.tseitinVarCounter++,
                partition);
    }

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
        if (clause == null)
            return null;
        Formula formula = clause.transformToConsequentsForm();
        assert (formula instanceof OrFormula);
        List<Formula> disjuncts = ((OrFormula) formula).getDisjuncts();
        if (disjuncts.size() != 1)
            assert (false);
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
            return new NotFormula(literal);

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
     * @param resolutionAssociate
     * @param transformedAntecedent
     * @return
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
                    reverseInverseLiteral = Util
                            .getSingleLiteral((new NotFormula(reverseLiteral))
                                    .transformToConsequentsForm());
                else
                    reverseInverseLiteral = Util
                            .getSingleLiteral(reverseLiteral
                                    .transformToConsequentsForm());
                if (clause2.getDisjuncts().contains(reverseInverseLiteral))
                    return Util.makeLiteralPositive(reverseInverseLiteral);
            }

        }
        throw new RuntimeException(
                "Did not find a matching literal in clauses.");
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

    private static String makeIdString(Formula formula) {

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

    private static boolean getSignValue(Formula literal) {

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

            List<Lit> resClause = new ArrayList<Lit>();
            // TODO: check if correct
            Set<Integer> resClausePartitions = new HashSet<Integer>();

            for (Formula literal : ((OrFormula) clause).getDisjuncts()) {

                // assign literal IDs
                Formula posLiteral = Util.makeLiteralPositive(literal);
                assert (Util.isLiteral(posLiteral));
                assert (Util.isAtom(posLiteral));

                if (posLiteral.equals(new PropositionalConstant(false))) {
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

                    Util.resProof.var_part[resLiteralID] = partition < 0 ? 0
                            : partition;
                }
                resClause
                        .add(new Lit(resLiteralID, Util.getSignValue(literal)));
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

                resLeafNode = Util.resProof.addLeaf(resClause, leafPartition);

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
        Formula tmp = formula.transformToConsequentsForm();
        if (!Util.isLiteral(tmp))
            return false;
        tmp = Util.getSingleLiteral(tmp);
        if (!(tmp instanceof EqualityFormula))
            return false;

        EqualityFormula equality = (EqualityFormula) tmp;

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

        if (node.getConsequent().equals(new PropositionalConstant(false)))
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
     * @param transformedZ3Proof
     * @return
     */
    public static int getSinglePartitionOfProof(
            TransformedZ3Proof transformedZ3Proof) {
        Set<Integer> partitions = transformedZ3Proof.getConsequent()
                .getPartitionsFromSymbols();
        if (partitions.size() == 1)
            return partitions.iterator().next();
        partitions.remove(-1);
        assert (partitions.size() == 1);
        return partitions.iterator().next();
    }

}
