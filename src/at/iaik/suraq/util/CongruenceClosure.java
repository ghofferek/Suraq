/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.List;
import java.util.Set;
import java.util.concurrent.CopyOnWriteArraySet;

import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;

/**
 * Helper Class to perform congruence closure algorithm.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class CongruenceClosure {

    /**
     * The list of equivalence classes
     */
    private final Set<Set<Term>> equivClasses = new CopyOnWriteArraySet<Set<Term>>();

    public CongruenceClosure() {
        // nothing to do here
    }

    /**
     * Adds the given equality and updates internal data structures (merging).
     * 
     * @param formula
     *            an equality formula with exactly two terms.
     */
    public void addEquality(EqualityFormula formula) {
        assert (formula.getTerms().size() == 2);
        assert (formula.isEqual());
        Term term1 = formula.getTerms().get(0);
        Term term2 = formula.getTerms().get(1);

        for (Set<Term> equivClass : equivClasses) {
            if (equivClass.contains(term1)) {
                equivClass.add(term2);
                merge();
                return;
            }
            if (equivClass.contains(term2)) {
                equivClass.add(term1);
                merge();
                return;
            }
        }

        Set<Term> newClass = new CopyOnWriteArraySet<Term>();
        newClass.add(term1);
        newClass.add(term2);
        equivClasses.add(newClass);
        merge();
        return;
    }

    /**
     * Checks whether the given formula is implied by this congruence closure.
     * I.e., checks whether its two terms occur in the same equivalence class.
     * 
     * @param formula
     * @return <code>true</code> if the given formula is implied by this
     *         congruence closure.
     */
    public boolean checkImplied(EqualityFormula formula) {
        assert (formula.getTerms().size() == 2);
        assert (formula.isEqual());
        Term term1 = formula.getTerms().get(0);
        Term term2 = formula.getTerms().get(1);

        for (Set<Term> equivClass : equivClasses) {
            if (equivClass.contains(term1) && equivClass.contains(term2))
                return true;
        }
        return false;
    }

    /**
     * Performs merging. Probably not very efficient.
     */
    private void merge() {
        while (mergeInternal()) {
            // Nothing; mergeInternal does everything
        }

    }

    /**
     * Performs one merge and reports back that it happened.
     * 
     * @return <code>true</code> if a merge was performed.
     */
    private boolean mergeInternal() {

        // Merging based on common terms
        for (Set<Term> equivClass1 : equivClasses) {
            assert (equivClasses.contains(equivClass1));
            for (Term term : equivClass1) {
                for (Set<Term> equivClass2 : equivClasses) {
                    assert (equivClasses.contains(equivClass2));
                    if (equivClass1 == equivClass2)
                        continue;
                    if (equivClass2.contains(term)) {
                        equivClass1.addAll(equivClass2);
                        equivClasses.remove(equivClass2);
                        return true;
                    }
                }
            }
        }

        // Merging based on congruence
        for (Set<Term> equivClass1 : equivClasses) {
            for (Term term1 : equivClass1) {
                List<DomainTerm> terms1 = null;
                List<DomainTerm> terms2 = null;
                Set<Term> equivClass2 = null;
                if (term1 instanceof UninterpretedFunctionInstance) {
                    terms1 = ((UninterpretedFunctionInstance) term1)
                            .getParameters();
                    for (Set<Term> equivClassTmp : equivClasses) {
                        if (equivClass1 == equivClassTmp)
                            continue;
                        for (Term term2 : equivClassTmp) {
                            if (term2 instanceof UninterpretedFunctionInstance) {
                                if (((UninterpretedFunctionInstance) term2)
                                        .getFunction()
                                        .equals(((UninterpretedFunctionInstance) term1)
                                                .getFunction())) {
                                    terms2 = ((UninterpretedFunctionInstance) term2)
                                            .getParameters();
                                    equivClass2 = equivClassTmp;
                                    break;
                                }
                            }
                        }
                        if (terms2 != null)
                            break;
                    }
                } else if (term1 instanceof UninterpretedPredicateInstance) {
                    terms1 = ((UninterpretedPredicateInstance) term1)
                            .getParameters();
                    for (Set<Term> equivClassTmp : equivClasses) {
                        if (equivClass1 == equivClassTmp)
                            continue;
                        for (Term term2 : equivClassTmp) {
                            if (term2 instanceof UninterpretedPredicateInstance) {
                                if (((UninterpretedFunctionInstance) term2)
                                        .getFunction()
                                        .equals(((UninterpretedPredicateInstance) term1)
                                                .getFunction())) {
                                    terms2 = ((UninterpretedPredicateInstance) term2)
                                            .getParameters();
                                    equivClass2 = equivClassTmp;
                                    break;
                                }
                            }
                        }
                        if (terms2 != null)
                            break;
                    }
                } else {
                    continue;
                }
                if (terms1 != null && terms2 != null) {
                    assert (equivClass2 != null);
                    assert (terms1.size() == terms2.size());
                    int numOk = 0;
                    for (int count = 0; count < terms1.size(); count++) {
                        for (Set<Term> equivClassTmp : equivClasses) {
                            if (equivClassTmp.contains(terms1.get(count))
                                    && equivClassTmp
                                            .contains(terms2.get(count))) {
                                numOk++;
                            }
                        }
                    }
                    if (numOk == terms1.size()) {
                        equivClass1.addAll(equivClass2);
                        equivClasses.remove(equivClass2);
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /**
     * 
     * @param node
     * @return <code>true</code> if the given <code>node</code> is a theory
     *         tautology.
     */
    public static boolean checkVeritProofNode(VeritProofNode node) {
        assert (node.getSubProofs().isEmpty());
        CongruenceClosure cc = new CongruenceClosure();
        for (Formula literal : node.getLiteralConclusions().subList(0,
                node.getLiteralConclusions().size() - 1)) {
            assert (Util.isNegativeLiteral(literal));
            Formula positiveLiteral = Util.makeLiteralPositive(literal);
            assert (positiveLiteral instanceof EqualityFormula);
            cc.addEquality((EqualityFormula) positiveLiteral);
        }
        Formula impliedLiteral = node.getLiteralConclusions().get(
                node.getLiteralConclusions().size() - 1);
        assert (Util.isLiteral(impliedLiteral));
        assert (!Util.isNegativeLiteral(impliedLiteral));
        assert (impliedLiteral instanceof EqualityFormula);
        return cc.checkImplied((EqualityFormula) impliedLiteral);
    }

}
