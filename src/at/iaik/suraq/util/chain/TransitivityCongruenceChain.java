/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util.chain;

import at.iaik.suraq.smtlib.formula.DomainTerm;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TransitivityCongruenceChain {

    /**
     * The starting point of the chain.
     */
    private final TransitivityCongruenceChainElement start;

    /**
     * The target of the chain.
     */
    private final DomainTerm target;

    /**
     * 
     * Constructs a new <code>TransitivityCongruenceChain</code>.
     * 
     * @param start
     * @param target
     */
    public TransitivityCongruenceChain(DomainTerm start, DomainTerm target) {
        assert (start != null);
        assert (target != null);
        this.start = new TransitivityCongruenceChainElement(start);
        this.target = target;
    }

    /**
     * 
     * @return the term (currently) at the end of this chain.
     */
    public DomainTerm getEndTerm() {
        TransitivityCongruenceChainElement current = start;
        assert (current != null);
        while (current.getNext() != null)
            current = current.getNext();
        assert (current != null);
        return current.getTerm();
    }

    /**
     * 
     * @return <code>true</code> if this chain has reached its target.
     */
    public boolean isComplete() {
        assert (target != null);
        return target.equals(getEndTerm());
    }

}
