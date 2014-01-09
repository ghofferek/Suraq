/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.util.chain.TransitivityCongruenceChain;

/**
 * A container for a justification of an equality between to terms in an
 * equality graph. Either contains an equality formula, or a set of
 * transitivity-congruence chains.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class Justification implements Copyable<Justification> {

    /**
     * The equality justification, or <code>null</code>
     */
    private final DomainEq equality;

    /**
     * The congruence justification, or <code>null</code>
     */
    private final ImmutableArrayList<TransitivityCongruenceChain> chains;

    /**
     * 
     * Constructs a new <code>Justification</code> based on
     * <code>equality</code>.
     * 
     * @param equality
     */
    public Justification(DomainEq equality) {
        assert (equality.isEqual());
        this.equality = equality;
        this.chains = null;
    }

    /**
     * 
     * Constructs a new <code>Justification</code> based on <code>chains</code>.
     * 
     * @param chains
     */
    public Justification(List<TransitivityCongruenceChain> chains) {
        this.equality = null;
        this.chains = new ImmutableArrayList<TransitivityCongruenceChain>(
                chains);
    }

    /**
     * 
     * @return <code>true</code> if this is an equality justification.
     */
    public boolean isEqualityJustification() {
        if (equality == null) {
            assert (chains != null);
            return false;
        } else {
            assert (chains == null);
            return true;
        }
    }

    /**
     * 
     * @return <code>true</code> if this is a congruence justification.
     */
    public boolean isCongruenceJustification() {
        if (chains == null) {
            assert (equality != null);
            return false;
        } else {
            assert (equality == null);
            return true;
        }
    }

    /**
     * 
     * @return the equality justification or <code>null</code> if this is a
     *         congruence justification.
     */
    public DomainEq getEqualityJustification() {
        return equality;
    }

    /**
     * 
     * @return the congruence justification or <code>null</code> if this is an
     *         equality justification.
     */
    public ImmutableArrayList<TransitivityCongruenceChain> getCongruenceJustification() {
        return chains;
    }

    /**
     * If this is an equality justification, <code>this</code> is returned.
     * Otherwise a new object with reversed chains is returned.
     * 
     * @return <code>this</code> or a reversed congruence justification.
     */
    public Justification reverse() {
        if (equality != null) {
            assert (chains == null);
            return this;
        } else {
            assert (chains != null);
            List<TransitivityCongruenceChain> reverseChains = new ArrayList<TransitivityCongruenceChain>(
                    chains.size());
            for (TransitivityCongruenceChain chain : chains) {
                reverseChains.add(chain.reverse());
            }
            return new Justification(reverseChains);
        }
    }

    /**
     * Returns a clone of this object. Equality justifications are copied
     * shallowly (as they are immutable anyway), congruence justifications are
     * copied deeply.
     * 
     * @see java.lang.Object#clone()
     */
    @Override
    public Justification clone() {
        if (equality != null) {
            assert (chains == null);
            return new Justification(equality);
        }
        if (chains != null) {
            assert (equality == null);
            List<TransitivityCongruenceChain> clonedChains = new ArrayList<TransitivityCongruenceChain>(
                    chains.size());
            for (TransitivityCongruenceChain chain : chains) {
                clonedChains.add(chain.clone());
            }
            return new Justification(clonedChains);
        }
        assert (false);
        return null;
    }
}
