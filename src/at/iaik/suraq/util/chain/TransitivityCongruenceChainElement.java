/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util.chain;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.exceptions.WrongFunctionTypeException;
import at.iaik.suraq.exceptions.WrongNumberOfParametersException;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.util.Justification;
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
     * Convenience method that constructs the <code>nextTerm</code>
     * automatically.
     * 
     * @param justification
     * @return <code>true</code> if attachment was successfull
     */
    protected boolean tryAttach(List<TransitivityCongruenceChain> justification) {
        if (!(this.term instanceof UninterpretedFunctionInstance))
            return false;
        UninterpretedFunction function = ((UninterpretedFunctionInstance) this.term)
                .getFunction();
        if (justification.size() != function.getNumParams())
            return false;
        List<DomainTerm> parameters = new ArrayList<DomainTerm>();
        for (TransitivityCongruenceChain chain : justification)
            parameters.add(chain.getEndTerm());
        try {
            UninterpretedFunctionInstance nextTerm = UninterpretedFunctionInstance
                    .create(function, parameters);
            return tryAttach(nextTerm, justification);
        } catch (WrongNumberOfParametersException exc) {
            return false;
        } catch (WrongFunctionTypeException exc) {
            return false;
        }

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
            if (!currentChain.getStart().getTerm()
                    .equals(parameters1.get(count)))
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
        this.congruenceJustification = null;
        this.equalityJustification = null;
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

    /**
     * @return the set of partitions formed by all symbols in this chain
     *         element.
     */
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> result = new HashSet<Integer>();
        result.addAll(term.getPartitionsFromSymbols());
        if (equalityJustification != null)
            result.addAll(equalityJustification.getPartitionsFromSymbols());
        if (congruenceJustification != null) {
            for (TransitivityCongruenceChain chain : congruenceJustification)
                result.addAll(chain.getPartitionsFromSymbols());
        }
        return result;
    }

    /**
     * 
     * @return the partition of the term of this element.
     */
    public int getTermPartition() {
        Set<Integer> partitions = this.term.getPartitionsFromSymbols();
        if (partitions.size() > 1)
            partitions.remove(-1);
        assert (partitions.size() == 1);
        return partitions.iterator().next();
    }

    /**
     * @return
     */
    public Justification getJustficiation() {
        if (equalityJustification == null ^ congruenceJustification == null) {
            if (equalityJustification == null) {
                return new Justification(congruenceJustification);
            } else {
                return new Justification(equalityJustification);
            }
        } else
            return null;
    }

    /**
     * @return
     */
    public boolean isCongruenceOfLocalFunctionOverOtherPartition() {
        if (this.congruenceJustification == null)
            return false;

        if (this.equalityJustification != null)
            return false;

        if (this.term == null)
            return false;

        if (!(this.term instanceof UninterpretedFunctionInstance))
            return false;

        UninterpretedFunctionInstance term1 = (UninterpretedFunctionInstance) this.term;

        if (this.next == null)
            return false;

        if (next.term == null)
            return false;

        if (!(next.term instanceof UninterpretedFunctionInstance))
            return false;

        UninterpretedFunctionInstance term2 = (UninterpretedFunctionInstance) next.term;

        if (!term1.getFunction().equals(term2.getFunction()))
            return false;

        if (Util.isGlobal(term1))
            return false;

        if (Util.isGlobal(term2))
            return false;

        Set<Integer> partitions = this.getPartitionsFromSymbols();
        partitions.remove(-1);

        if (partitions.size() <= 1)
            return false;

        return true;
    }

    /**
     * @param partitions
     * @return
     */
    public boolean isCongruenceOverOtherPartition(Set<Integer> partitions) {
        assert (partitions != null);
        assert (!partitions.contains(-1));
        assert (partitions.size() <= 1);

        if (this.congruenceJustification == null)
            return false;

        if (this.equalityJustification != null)
            return false;

        if (this.term == null)
            return false;

        if (!(this.term instanceof UninterpretedFunctionInstance))
            return false;

        UninterpretedFunctionInstance term1 = (UninterpretedFunctionInstance) this.term;

        if (this.next == null)
            return false;

        if (next.term == null)
            return false;

        if (!(next.term instanceof UninterpretedFunctionInstance))
            return false;

        UninterpretedFunctionInstance term2 = (UninterpretedFunctionInstance) next.term;

        if (!term1.getFunction().equals(term2.getFunction()))
            return false;

        Set<Integer> partitionsOfThis = this.getPartitionsFromSymbols();
        partitionsOfThis.remove(-1);

        if (partitionsOfThis.size() != 1)
            return false;

        partitionsOfThis.addAll(partitions);
        if (partitionsOfThis.size() == 1)
            return false;

        return true;
    }

    /**
     * For a congruence link to be colorable, all equalities for the parameters
     * as well as the implied literal (equality between function instances) have
     * to be colorable with one color. Internally, the equalities for the
     * parameters may use different colors, but they must be "summarizable" by
     * literals of one color. This method does <strong>not</strong> do a
     * recursive check!
     * 
     * @return <code>true</code> iff this element has a colorable congruence
     *         justification.
     */
    public boolean hasColorableCongruenceJustification() {
        assert (this.congruenceJustification != null);
        assert (this.equalityJustification == null);

        Set<Integer> partitions = this.term.getPartitionsFromSymbols();
        partitions.addAll(this.next.term.getPartitionsFromSymbols());
        for (TransitivityCongruenceChain chain : this.congruenceJustification) {
            partitions.add(chain.getStartPartition());
            partitions.add(chain.getEndPartition());
        }
        partitions.remove(-1);
        return partitions.size() <= 1;
    }
}
