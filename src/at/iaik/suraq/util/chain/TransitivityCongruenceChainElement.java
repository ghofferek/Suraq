/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util.chain;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.util.Util;

/**
 * An element in a transitivity-congruence chain.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TransitivityCongruenceChainElement {

    /**
     * The term that this element represents.
     */
    private final DomainTerm term;

    /**
     * Pointer to next element in the chain.
     */
    private TransitivityCongruenceChainElement next = null;

    /**
     * The equality justifying the link to the next element, or
     * <code>null</code> if it is a congruence link.
     */
    private DomainEq equalityJustification = null;

    /**
     * The list of chains justifying the link to the next element, of
     * <code>null</code> if it is an equality link.
     */
    private List<TransitivityCongruenceChain> congruenceJustification = null;

    /**
     * 
     * Constructs a new <code>TransitivityCongruenceChainElement</code>.
     * 
     * @param term
     */
    protected TransitivityCongruenceChainElement(DomainTerm term) {
        assert (term != null);
        this.term = term;
    }

    /**
     * Constructs a new <code>TransitivityCongruenceChainElement</code>.
     * 
     * @param element
     */
    protected TransitivityCongruenceChainElement(
            TransitivityCongruenceChainElement element) {
        this.term = element.term;
        this.next = element.next;
        this.equalityJustification = element.equalityJustification;
        this.congruenceJustification = element.congruenceJustification;
    }

    /**
     * Tries to attach the given <code>equality</code> to this chain element. If
     * <code>next</code> is not <code>null</code> attachment will fail.
     * 
     * @param equality
     * @return <code>true</code> if the given equality could be attached.
     */
    protected boolean tryAttach(DomainEq equality) {
        if (next != null)
            return false;
        assert (equality != null);
        assert (equality.isEqual());
        assert (equality.getTerms().size() == 2);
        assert (equality.getTerms().get(0) instanceof DomainTerm);
        assert (equality.getTerms().get(1) instanceof DomainTerm);

        if (this.term.equals(equality.getTerms().get(0))) {
            assert (next == null);
            this.next = new TransitivityCongruenceChainElement(
                    (DomainTerm) equality.getTerms().get(1));
            assert (next != null);
            this.equalityJustification = equality;
            assert (congruenceJustification == null);
            return true;
        }

        if (this.term.equals(equality.getTerms().get(1))) {
            assert (next == null);
            this.next = new TransitivityCongruenceChainElement(
                    (DomainTerm) equality.getTerms().get(0));
            assert (next != null);
            this.equalityJustification = equality;
            assert (congruenceJustification == null);
            return true;
        }

        assert (!this.term.equals(equality.getTerms().get(0)) && !this.term
                .equals(equality.getTerms().get(1)));
        assert (next == null);
        assert (equalityJustification == null);
        assert (congruenceJustification == null);
        return false;
    }

    protected boolean tryAttach(UninterpretedFunctionInstance nextTerm,
            List<TransitivityCongruenceChain> justification) {
        if (next != null)
            return false;
        assert (next == null);
        assert (equalityJustification == null);
        assert (congruenceJustification == null);
        assert (nextTerm != null);
        assert (justification != null);
        assert (!justification.isEmpty());
        if (!(this.term instanceof UninterpretedFunctionInstance))
            return false;
        if (!nextTerm.getFunction().equals(
                ((UninterpretedFunctionInstance) this.term).getFunction()))
            return false;
        if (!checkJustification(justification,
                ((UninterpretedFunctionInstance) this.term).getParameters(),
                nextTerm.getParameters()))
            return false;
        this.congruenceJustification = new ArrayList<TransitivityCongruenceChain>(
                justification);
        this.next = new TransitivityCongruenceChainElement(nextTerm);
        assert (next != null);
        assert (congruenceJustification != null);
        assert (equalityJustification == null);
        return true;
    }

    /**
     * @param justification
     * @param parameters1
     * @param parameters2
     * @return
     */
    private boolean checkJustification(
            List<TransitivityCongruenceChain> justification,
            List<DomainTerm> parameters1, List<DomainTerm> parameters2) {

        if (justification.size() != parameters1.size())
            return false;

        if (justification.size() != parameters2.size())
            return false;

        assert (parameters1.size() == parameters2.size());

        for (int count = 0; count < justification.size(); count++) {
            TransitivityCongruenceChain currentChain = justification.get(count);
            if (!currentChain.isComplete())
                return false;
            if (!currentChain.getStart().equals(parameters1.get(count)))
                return false;
            if (!currentChain.getTarget().equals(parameters2.get(count)))
                return false;
        }

        return true;
    }

    /**
     * 
     * @return a set of formulas used as link in this element.
     */
    protected Set<Formula> usedLiterals() {
        Set<Formula> result = new HashSet<Formula>();
        if (equalityJustification != null) {
            assert (congruenceJustification == null);
            result.add(equalityJustification);
        } else if (congruenceJustification != null) {
            assert (equalityJustification == null);
            assert (!congruenceJustification.isEmpty());
            for (TransitivityCongruenceChain chain : congruenceJustification)
                result.addAll(chain.usedLiterals());
        }
        return result;
    }

    /**
     * @return the <code>term</code>
     */
    public DomainTerm getTerm() {
        return term;
    }

    /**
     * @return the <code>next</code>
     */
    public TransitivityCongruenceChainElement getNext() {
        return next;
    }

    /**
     * 
     * @return <code>true</code> if there is a next element.
     */
    public boolean hasNext() {
        return next != null;
    }

    /**
     * @return the <code>equalityJustification</code>
     */
    public DomainEq getEqualityJustification() {
        return equalityJustification;
    }

    /**
     * @return the <code>congruenceJustification</code>
     */
    public List<TransitivityCongruenceChain> getCongruenceJustification() {
        return congruenceJustification;
    }

    /**
     * @return <code>true</code> if the term of this element is global.
     */
    public boolean isGlobal() {
        Set<Integer> partitions = term.getPartitionsFromSymbols();
        partitions.remove(-1);
        return partitions.isEmpty();
    }

    /**
     * 
     */
    protected void makeNextNull() {
        this.next = null;
    }

    /**
     * 
     */
    protected void attachReflexivity() {
        assert (this.next == null);
        assert (this.equalityJustification == null);
        assert (this.congruenceJustification == null);
        this.next = new TransitivityCongruenceChainElement(this.term);
        this.equalityJustification = Util.createReflexivity(this.term);
    }

    /**
     * @param patch
     */
    protected void makeLeftSplice(TransitivityCongruenceChainElement patch) {
        assert (this.term.equals(patch.term));
        this.next = patch.next;
        this.equalityJustification = patch.equalityJustification;
        this.congruenceJustification = patch.congruenceJustification;
        assert (this.congruenceJustification == null ^ this.equalityJustification == null);
    }

    /**
     * @param patch
     */
    protected void makeRightSplice(TransitivityCongruenceChainElement patch) {
        assert (this.term.equals(patch.term));
        patch.next = this.next;
        patch.equalityJustification = this.equalityJustification;
        patch.congruenceJustification = this.congruenceJustification;
        assert ((patch.congruenceJustification == null ^ patch.equalityJustification == null) || (patch.next == null
                && patch.congruenceJustification == null && patch.equalityJustification == null));
    }

}
