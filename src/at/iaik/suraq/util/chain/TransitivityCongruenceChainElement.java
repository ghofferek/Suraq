/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util.chain;

import java.util.List;

import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;

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
    public TransitivityCongruenceChainElement(DomainTerm term) {
        assert (term != null);
        this.term = term;
    }

    /**
     * Tries to attach the given <code>equality</code> to this chain element. If
     * <code>next</code> is not <code>null</code> attachment will fail.
     * 
     * @param equality
     * @return <code>true</code> if the given equality could be attached.
     */
    public boolean tryAttach(DomainEq equality) {
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

}
