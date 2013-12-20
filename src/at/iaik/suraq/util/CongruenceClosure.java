/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CopyOnWriteArraySet;

import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
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
     * Counts calls to checkTheoryLemma
     */
    private static long checkTheoryLemmaCounter = 0;

    /**
     * Stores timing for checkTheoryLemma calls
     */
    private static final Timer checkTheoryLemmaTimer = new Timer();

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

        if (term1 instanceof UninterpretedFunctionInstance) {
            this.addTerm(term1);
        }
        if (term2 instanceof UninterpretedFunctionInstance) {
            this.addTerm(term2);
        }

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
     * 
     * @return the number of equivalence classes
     */
    public int getNumEquivClasses() {
        return this.equivClasses.size();
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
                        boolean removed = equivClasses.remove(equivClass2);
                        assert (removed);
                        return true;
                    }
                }
            }
        }

        // Merging based on congruence

        Map<UninterpretedFunctionInstance, Set<DomainTerm>> functionInstancesEquivClasses = getAllUninterpretedFunctionInstances();

        for (UninterpretedFunctionInstance instance1 : functionInstancesEquivClasses
                .keySet()) {
            for (UninterpretedFunctionInstance instance2 : functionInstancesEquivClasses
                    .keySet()) {
                if (instance1 == instance2)
                    continue;
                if (functionInstancesEquivClasses.get(instance1) == functionInstancesEquivClasses
                        .get(instance2))
                    continue;
                if (!instance1.getFunction().equals(instance2.getFunction()))
                    continue;

                assert (instance1.getParameters().size() == instance2
                        .getParameters().size());

                int numOk = 0;
                for (int count = 0; count < instance1.getParameters().size(); count++) {
                    DomainTerm param1 = instance1.getParameters().get(count);
                    DomainTerm param2 = instance2.getParameters().get(count);
                    if (findClassContainingBoth(param1, param2) != null)
                        numOk++;
                }
                if (numOk == instance1.getParameters().size()) {
                    Set<DomainTerm> class1 = functionInstancesEquivClasses
                            .get(instance1);
                    Set<DomainTerm> class2 = functionInstancesEquivClasses
                            .get(instance2);
                    class1.addAll(class2);
                    boolean removed = this.equivClasses.remove(class2);
                    assert (removed);
                    return true;
                }
            }
        }

        return false;

        // for (Set<DomainTerm> equivClass1 : equivClasses) {
        // for (Term term1 : equivClass1) {
        // List<DomainTerm> terms1 = null;
        // List<DomainTerm> terms2 = null;
        // Set<DomainTerm> equivClass2 = null;
        // if (term1 instanceof UninterpretedFunctionInstance) {
        // terms1 = ((UninterpretedFunctionInstance) term1)
        // .getParameters();
        // for (Set<DomainTerm> equivClassTmp : equivClasses) {
        // if (equivClass1 == equivClassTmp)
        // continue;
        // for (Term term2 : equivClassTmp) {
        // if (term2 instanceof UninterpretedFunctionInstance) {
        // if (((UninterpretedFunctionInstance) term2)
        // .getFunction()
        // .equals(((UninterpretedFunctionInstance) term1)
        // .getFunction())) {
        // terms2 = ((UninterpretedFunctionInstance) term2)
        // .getParameters();
        // equivClass2 = equivClassTmp;
        // break;
        // }
        // }
        // }
        // if (terms2 != null)
        // break;
        // }
        // } else if (term1 instanceof UninterpretedPredicateInstance) {
        // terms1 = ((UninterpretedPredicateInstance) term1)
        // .getParameters();
        // for (Set<DomainTerm> equivClassTmp : equivClasses) {
        // if (equivClass1 == equivClassTmp)
        // continue;
        // for (Term term2 : equivClassTmp) {
        // if (term2 instanceof UninterpretedPredicateInstance) {
        // if (((UninterpretedFunctionInstance) term2)
        // .getFunction()
        // .equals(((UninterpretedPredicateInstance) term1)
        // .getFunction())) {
        // terms2 = ((UninterpretedPredicateInstance) term2)
        // .getParameters();
        // equivClass2 = equivClassTmp;
        // break;
        // }
        // }
        // }
        // if (terms2 != null)
        // break;
        // }
        // } else {
        // continue;
        // }
        // if (terms1 != null && terms2 != null) {
        // assert (equivClass2 != null);
        // assert (terms1.size() == terms2.size());
        // int numOk = 0;
        // for (int count = 0; count < terms1.size(); count++) {
        // for (Set<DomainTerm> equivClassTmp : equivClasses) {
        // if (equivClassTmp.contains(terms1.get(count))
        // && equivClassTmp
        // .contains(terms2.get(count))) {
        // numOk++;
        // }
        // }
        // }
        // if (numOk == terms1.size()) {
        // equivClass1.addAll(equivClass2);
        // equivClasses.remove(equivClass2);
        // return true;
        // }
        // }
        // }
        // }
        // return false;
    }

    /**
     * 
     * @param term1
     * @param term2
     * @return the equivalence class that holds both <code>term1</code> and
     *         <code>term2</code>, or <code>null</code> if no such class exists
     */
    private Set<DomainTerm> findClassContainingBoth(DomainTerm term1,
            DomainTerm term2) {
        for (Set<DomainTerm> equivClass : this.equivClasses) {
            if (equivClass.contains(term1) && equivClass.contains(term2))
                return equivClass;
        }
        return null;
    }

    /**
     * Returns a map with all uninterpreted function instances as keys, mapping
     * to the equivalence classes they are currently in.
     * 
     * @return a map from uninterpreted function instances to containing
     *         equivalence classes.
     */
    private Map<UninterpretedFunctionInstance, Set<DomainTerm>> getAllUninterpretedFunctionInstances() {
        Map<UninterpretedFunctionInstance, Set<DomainTerm>> result = new HashMap<UninterpretedFunctionInstance, Set<DomainTerm>>();
        for (Set<DomainTerm> equivClass : this.equivClasses) {
            for (DomainTerm term : equivClass) {
                if (term instanceof UninterpretedFunctionInstance)
                    result.put((UninterpretedFunctionInstance) term, equivClass);
            }
        }
        return result;
    }

    /**
     * This check assumes that only one positive literal is present in the
     * <code>literals</code>. If the given literals contains anything that
     * should not occur in a theory lemma (e.g. Tseitin variables)
     * <code>false</code> is returned.
     * 
     * @param literals
     *            a collection of literals (only one positive)
     * @return <code>true</code> if the given <code>literals</code> are a theory
     *         lemma
     */
    public static boolean checkTheoryLemma(
            Collection<? extends Formula> literals) {
        CongruenceClosure.checkTheoryLemmaTimer.start();
        CongruenceClosure.checkTheoryLemmaCounter++;
        assert (literals != null);
        CongruenceClosure cc = new CongruenceClosure();
        Formula impliedLiteral = null;
        for (Formula literal : literals) {
            if (literal instanceof PropositionalVariable) {
                // e.g. Tseitin variable, or something from the input
                CongruenceClosure.checkTheoryLemmaTimer.stop();
                return false;
            }
            if (Util.isNegativeLiteral(literal)) {
                Formula positiveLiteral = Util.makeLiteralPositive(literal);
                if (positiveLiteral instanceof DomainEq) {
                    cc.addEquality((DomainEq) positiveLiteral);
                }
            } else {
                if (impliedLiteral != null) {
                    // More than one implied literal means this is not a theory
                    // lemma
                    CongruenceClosure.checkTheoryLemmaTimer.stop();
                    return false;
                }

                assert (Util.isAtom(literal));
                impliedLiteral = literal;
            }
        }
        if (impliedLiteral == null) {
            // No implied literal means this is not a theory lemma
            CongruenceClosure.checkTheoryLemmaTimer.stop();
            return false;
        }
        assert (Util.isLiteral(impliedLiteral));
        assert (!Util.isNegativeLiteral(impliedLiteral));

        if (impliedLiteral instanceof DomainEq) {
            assert (((DomainEq) impliedLiteral).getTerms().size() == 2);
            cc.addTerm((DomainTerm) ((DomainEq) impliedLiteral).getTerms().get(
                    0));
            cc.addTerm((DomainTerm) ((DomainEq) impliedLiteral).getTerms().get(
                    1));
            cc.merge();
            final boolean result = cc.checkImplied((DomainEq) impliedLiteral);
            CongruenceClosure.checkTheoryLemmaTimer.stop();
            return result;
        } else {
            assert (impliedLiteral instanceof UninterpretedPredicateInstance);
            UninterpretedPredicateInstance positiveInstance = (UninterpretedPredicateInstance) impliedLiteral;
            UninterpretedPredicateInstance negativeInstance = null;
            for (Formula literal : literals) {
                if (!Util.isNegativeLiteral(literal))
                    continue;
                Formula positiveLiteral = Util.makeLiteralPositive(literal);
                if (!(positiveLiteral instanceof UninterpretedPredicateInstance))
                    continue;
                UninterpretedPredicateInstance predicateInstance = (UninterpretedPredicateInstance) positiveLiteral;
                if (!predicateInstance.getFunction().equals(
                        positiveInstance.getFunction()))
                    continue;
                if (negativeInstance != null) {
                    // Only one matching instance should exist in a theory lemma
                    CongruenceClosure.checkTheoryLemmaTimer.stop();
                    return false;
                }
                negativeInstance = predicateInstance;
            }
            if (negativeInstance == null) {
                // No matching instance found
                // Not a theory lemma
                CongruenceClosure.checkTheoryLemmaTimer.stop();
                return false;
            }
            assert (positiveInstance.getFunction().equals(negativeInstance
                    .getFunction()));
            assert (positiveInstance.getFunction().getNumParams() == negativeInstance
                    .getFunction().getNumParams());
            assert (positiveInstance.getParameters().size() == negativeInstance
                    .getParameters().size());

            for (int count = 0; count < positiveInstance.getFunction()
                    .getNumParams(); count++) {
                DomainTerm term1 = positiveInstance.getParameters().get(count);
                DomainTerm term2 = negativeInstance.getParameters().get(count);
                List<DomainTerm> domainTerms = new ArrayList<DomainTerm>(2);
                domainTerms.add(term1);
                domainTerms.add(term2);
                DomainEq equalityToCheck = DomainEq.create(domainTerms, true);
                if (!cc.checkImplied(equalityToCheck)) {
                    CongruenceClosure.checkTheoryLemmaTimer.stop();
                    return false;
                }
            }
            CongruenceClosure.checkTheoryLemmaTimer.stop();
            return true;
        }
    }

    /**
     * This check assumes that only one positive literal is present in the
     * conclusion. This should hold for veriT proofs, because every (original)
     * theory-lemma leaf has only one positive literal and every resolution
     * eliminates one positive literal.
     * 
     * @param node
     * @return <code>true</code> if the given <code>node</code>'s conclusion is
     *         a theory lemma.
     */
    public static boolean checkVeritProofNode(VeritProofNode node) {
        return CongruenceClosure.checkTheoryLemma(node.getLiteralConclusions());
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

    /**
     * 
     * @return the counter of calls to <code>checkTheoryLemma</code>.
     */
    public static long getCheckTheoryLemmaCounter() {
        return CongruenceClosure.checkTheoryLemmaCounter;
    }

    /**
     * 
     * @return the value of the timer of the calls to
     *         <code>checkTheoryLemma</code>.
     */
    public static String getCheckTheoryLemmaTimer() {
        return CongruenceClosure.checkTheoryLemmaTimer.toString();
    }

}
