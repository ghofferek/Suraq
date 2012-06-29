/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.Iterator;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ImmutableIterator<E> implements Iterator<E> {

    private Iterator<E> internalIterator;

    public ImmutableIterator(Iterator<E> iterator) {
        internalIterator = iterator;
    }

    /**
     * @see java.util.Iterator#hasNext()
     */
    @Override
    public boolean hasNext() {

        return internalIterator.hasNext();
    }

    /**
     * @see java.util.Iterator#next()
     */
    @Override
    public E next() {
        return internalIterator.next();
    }

    /**
     * <strong>UNSUPPORTED OPERATION!</strong>
     * 
     * @see java.util.Iterator#remove()
     */
    @Override
    public void remove() {
        throw new UnsupportedOperationException(
                "'remove' called on immutable iterator!");
    }

}
