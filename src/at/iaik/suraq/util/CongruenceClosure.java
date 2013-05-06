/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.concurrent.CopyOnWriteArraySet;

import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.smtlib.formula.DomainEq;
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
    private final Set<Set<DomainTerm>> equivClasses = new CopyOnWriteArraySet<Set<DomainTerm>>();

    public CongruenceClosure() {
        // nothing to do here
    }

    /**
     * Adds the given equality and updates internal data structures (merging).
     * 
     * @param formula
     *            an equality formula with exactly two terms.
     */
    public void addEquality(DomainEq formula) {
        assert (formula.getTerms().size() == 2);
        assert (formula.isEqual());
        DomainTerm term1 = (DomainTerm) formula.getTerms().get(0);
        DomainTerm term2 = (DomainTerm) formula.getTerms().get(1);

        for (Set<DomainTerm> equivClass : equivClasses) {
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

        Set<DomainTerm> newClass = new CopyOnWriteArraySet<DomainTerm>();
        newClass.add(term1);
        newClass.add(term2);
        equivClasses.add(newClass);

        if (term1 instanceof UninterpretedFunctionInstance) {
            for (DomainTerm term : ((UninterpretedFunctionInstance) term1)
                    .getSubTerms()) {
                Set<DomainTerm> singleton = new CopyOnWriteArraySet<DomainTerm>();
                singleton.add(term);
                equivClasses.add(singleton);
            }
        }
        if (term2 instanceof UninterpretedFunctionInstance) {
            for (DomainTerm term : ((UninterpretedFunctionInstance) term2)
                    .getSubTerms()) {
                Set<DomainTerm> singleton = new CopyOnWriteArraySet<DomainTerm>();
                singleton.add(term);
                equivClasses.add(singleton);
            }
        }

        merge();
        return;
    }

    /**
     * Adds the given term to the equivalences classes. (Also adds all
     * subterms.)
     * 
     * @param term
     */
    public void addTerm(DomainTerm term) {
        if (term instanceof UninterpretedFunctionInstance) {
            for (DomainTerm subterm : ((UninterpretedFunctionInstance) term)
                    .getSubTerms())
                this.addTerm(subterm);
        }
        for (Set<DomainTerm> equivClass : equivClasses) {
            if (equivClass.contains(term))
                return;
        }
        Set<DomainTerm> singleton = new CopyOnWriteArraySet<DomainTerm>();
        singleton.add(term);
        equivClasses.add(singleton);
    }

    /**
     * Checks whether the given formula is implied by this congruence closure.
     * I.e., checks whether its two terms occur in the same equivalence class.
     * 
     * @param formula
     * @return <code>true</code> if the given formula is implied by this
     *         congruence closure.
     */
    public boolean checkImplied(DomainEq formula) {
        assert (formula.getTerms().size() == 2);
        assert (formula.isEqual());
        DomainTerm term1 = (DomainTerm) formula.getTerms().get(0);
        DomainTerm term2 = (DomainTerm) formula.getTerms().get(1);

        this.addTerm(term1);
        this.addTerm(term2);
        this.merge();

        for (Set<DomainTerm> equivClass : equivClasses) {
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
        for (Set<DomainTerm> equivClass1 : equivClasses) {
            assert (equivClasses.contains(equivClass1));
            for (DomainTerm term : equivClass1) {
                for (Set<DomainTerm> equivClass2 : equivClasses) {
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
        for (Set<DomainTerm> equivClass1 : equivClasses) {
            for (Term term1 : equivClass1) {
                List<DomainTerm> terms1 = null;
                List<DomainTerm> terms2 = null;
                Set<DomainTerm> equivClass2 = null;
                if (term1 instanceof UninterpretedFunctionInstance) {
                    terms1 = ((UninterpretedFunctionInstance) term1)
                            .getParameters();
                    for (Set<DomainTerm> equivClassTmp : equivClasses) {
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
                    for (Set<DomainTerm> equivClassTmp : equivClasses) {
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
                        for (Set<DomainTerm> equivClassTmp : equivClasses) {
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
            assert (positiveLiteral instanceof DomainEq);
            cc.addEquality((DomainEq) positiveLiteral);
        }
        Formula impliedLiteral = node.getLiteralConclusions().get(
                node.getLiteralConclusions().size() - 1);
        assert (Util.isLiteral(impliedLiteral));
        assert (!Util.isNegativeLiteral(impliedLiteral));
        assert (impliedLiteral instanceof DomainEq);
        assert (((DomainEq) impliedLiteral).getTerms().size() == 2);
        cc.addTerm((DomainTerm) ((DomainEq) impliedLiteral).getTerms().get(0));
        cc.addTerm((DomainTerm) ((DomainEq) impliedLiteral).getTerms().get(1));
        cc.merge();
        return cc.checkImplied((DomainEq) impliedLiteral);
    }

    /**
     * 
     * @param literals
     *            a collection of literals which are checked for whether they
     *            imply the given <code>impliedLiteral</code>. All these must be
     *            positive.
     * @param impliedLiteral
     *            the literal which should be implied by the given
     *            <code>literals</code>. Must be positive.
     * @return <code>true</code> if the given <code>literals</code> imply the
     *         given <code>impliedLiteral</code>.
     */
    public static boolean checkLiteralImplication(
            Collection<? extends EqualityFormula> literals,
            DomainEq impliedLiteral) {
        CongruenceClosure cc = new CongruenceClosure();
        for (Formula literal : literals) {
            assert (Util.isLiteral(literal));
            assert (!Util.isNegativeLiteral(literal));
            cc.addEquality((DomainEq) literal);
        }
        assert (Util.isLiteral(impliedLiteral));
        assert (!Util.isNegativeLiteral(impliedLiteral));
        return cc.checkImplied(impliedLiteral);
    }

    /**
     * 
     * @param literals
     *            a collection of literals which are checked for whether they
     *            imply the given <code>impliedLiteral</code>. All these must be
     *            positive.
     * @param term1
     *            the first term of the literal which should be implied by the
     *            given <code>literals</code>.
     * @param term2
     *            the second term of the literal which should be implied by the
     *            given <code>literals</code>.
     * @return <code>true</code> if the given <code>literals</code> imply the
     *         literal <code>term1=term2</code>.
     */
    public static boolean checkLiteralImplication(
            Collection<? extends EqualityFormula> literals, DomainTerm term1,
            DomainTerm term2) {
        List<DomainTerm> domainTerms = new ArrayList<DomainTerm>(2);
        domainTerms.add(term1);
        domainTerms.add(term2);
        DomainEq impliedLiteral = DomainEq.create(domainTerms, true);
        CongruenceClosure cc = new CongruenceClosure();
        cc.addTerm(term1);
        cc.addTerm(term2);
        for (Formula literal : literals) {
            assert (Util.isLiteral(literal));
            assert (!Util.isNegativeLiteral(literal));
            assert (literal instanceof DomainEq);
            cc.addEquality((DomainEq) literal);
        }
        assert (Util.isLiteral(impliedLiteral));
        assert (!Util.isNegativeLiteral(impliedLiteral));
        return cc.checkImplied(impliedLiteral);
    }

}
