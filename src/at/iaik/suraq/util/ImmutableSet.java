/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ImmutableSet<E> implements Set<E> {

    private Set<E> internalSet;

    private static Map<Set<?>, ImmutableSet<?>> instances = new HashMap<Set<?>, ImmutableSet<?>>();

    /**
     * Constructs a new <code>ImmutableSet</code>.
     * 
     * @param set
     */
    private ImmutableSet(Collection<? extends E> set) {
        internalSet = new HashSet<E>();
        internalSet.addAll(set);
        Set<E> key = new HashSet<E>();
        key.addAll(set);
        ImmutableSet.instances.put(key, this);
    }

    public static <T> ImmutableSet<T> create(Collection<? extends T> set) {

        ImmutableSet<?> existingSet = ImmutableSet.instances.get(set);
        if (existingSet != null) {
            assert (set.getClass().isInstance(existingSet));
            @SuppressWarnings("unchecked")
            ImmutableSet<T> castResult = (ImmutableSet<T>) existingSet;
            return castResult;
        }

        ImmutableSet<T> newSet = new ImmutableSet<T>(set);
        return newSet;
    }

    /**
     * @see java.util.Set#size()
     */
    @Override
    public int size() {

        return internalSet.size();
    }

    /**
     * @see java.util.Set#isEmpty()
     */
    @Override
    public boolean isEmpty() {

        return internalSet.isEmpty();
    }

    /**
     * @see java.util.Set#contains(java.lang.Object)
     */
    @Override
    public boolean contains(Object o) {

        return internalSet.contains(o);
    }

    /**
     * @see java.util.Set#iterator()
     */
    @Override
    public Iterator<E> iterator() {

        return new ImmutableIterator<E>(internalSet.iterator());
    }

    /**
     * @see java.util.Set#toArray()
     */
    @Override
    public Object[] toArray() {
        return internalSet.toArray();
    }

    /**
     * @see java.util.Set#toArray(T[])
     */
    @Override
    public <T> T[] toArray(T[] a) {
        return internalSet.toArray(a);
    }

    /**
     * <strong>UNSUPPORTED OPERATION!</strong>
     * 
     * @see java.util.Set#add(java.lang.Object)
     */
    @Override
    public boolean add(E e) {
        throw new UnsupportedOperationException(
                "'add' called on immutable set!");
    }

    /**
     * <strong>UNSUPPORTED OPERATION!</strong>
     * 
     * @see java.util.Set#remove(java.lang.Object)
     */
    @Override
    public boolean remove(Object o) {
        throw new UnsupportedOperationException(
                "'remove' called on immutable set!");
    }

    /**
     * @see java.util.Set#containsAll(java.util.Collection)
     */
    @Override
    public boolean containsAll(Collection<?> c) {
        return internalSet.containsAll(c);
    }

    /**
     * <strong>UNSUPPORTED OPERATION!</strong>
     * 
     * @see java.util.Set#addAll(java.util.Collection)
     */
    @Override
    public boolean addAll(Collection<? extends E> c) {
        throw new UnsupportedOperationException(
                "'addAll' called on immutable set!");
    }

    /**
     * <strong>UNSUPPORTED OPERATION!</strong>
     * 
     * @see java.util.Set#retainAll(java.util.Collection)
     */
    @Override
    public boolean retainAll(Collection<?> c) {
        throw new UnsupportedOperationException(
                "'retainAll' called on immutable set!");
    }

    /**
     * <strong>UNSUPPORTED OPERATION!</strong>
     * 
     * @see java.util.Set#removeAll(java.util.Collection)
     */
    @Override
    public boolean removeAll(Collection<?> c) {
        throw new UnsupportedOperationException(
                "'removeAll' called on immutable set!");
    }

    /**
     * <strong>UNSUPPORTED OPERATION!</strong>
     * 
     * @see java.util.Set#clear()
     */
    @Override
    public void clear() {
        throw new UnsupportedOperationException(
                "'removeAll' called on immutable set!");
    }
}
