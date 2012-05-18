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

    private static Map<String, Integer> literalsID = new HashMap<String, Integer>();
    private static Map<Integer, ResNode> resNodes = new HashMap<Integer, ResNode>();
    private static ResProof resProof;

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
        if (!Util.isUnitClause(formula1))
            return false;
        if (!Util.isUnitClause(formula2))
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

        // (a=b) (a!=b) (b!=a) (b=a) should have same IDs
        if (formula instanceof EqualityFormula) {
            ArrayList<String> terms = new ArrayList<String>();
            for (Term t : ((EqualityFormula) formula).getTerms())
                terms.add(t.toString());

            Collections.sort(terms);
            return terms.toString();
        } else
            return formula.toString();
    }

    private static boolean getSignValue(Formula formula) {

        assert (Util.isLiteral(formula));
        boolean sign = true;

        if (formula instanceof NotFormula) {
            sign = false;
            formula = ((NotFormula) formula).getNegatedFormula();
        }

        if (formula instanceof EqualityFormula) {
            if (((EqualityFormula) formula).isEqual())
                return sign;
            else
                return !sign;
        }
        return sign;
    }

    public static final ResProof createResolutionProof(TransformedZ3Proof proof) {

        Util.resProof = new ResProof();

        ResNode rootNode = Util.createResolutionProofRecursive(proof);
        Util.resProof.setRoot(rootNode);

        Util.literalsID.clear();
        Util.resNodes.clear();

        return Util.resProof;
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

                Integer resLiteralID = Util.literalsID.get(Util
                        .makeIdString(posLiteral));

                Set<Integer> partitions = literal.getPartitionsFromSymbols();
                if (partitions.size() == 2)
                    partitions.remove(-1);
                assert (partitions.size() == 1);
                int partition = partitions.iterator().next();

                if (resLiteralID == null) {
                    resLiteralID = Util.literalsID.size() + 1;
                    Util.literalsID.put(Util.makeIdString(posLiteral),
                            resLiteralID);

                    Util.resProof.var_part[resLiteralID] = partition;
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

                resLeafNode = Util.resProof.addLeaf(resClause,
                        resClausePartitions.iterator().next());

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
                    "Resolution proof should only consits of asserted and unit-resolution elements");

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
}
