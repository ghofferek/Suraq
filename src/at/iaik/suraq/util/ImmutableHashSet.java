/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.util;

import java.io.Serializable;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

/**
 * @author Christoph Hillebold <c.hillebold@student.tugraz.at>
 * 
 */
public class ImmutableHashSet<E> implements Set<E>, Serializable {

    private static final long serialVersionUID = 8782268576752007764L;
    private final Set<E> internalSet;
    private final int hashCode;

    /**
     * Constructs a new <code>ImmutableSet</code>.
     * 
     * @param set
     */
    public ImmutableHashSet(Collection<? extends E> set) {
        assert (set != null);
        internalSet = new HashSet<E>(set);
        this.hashCode = internalSet.hashCode();
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
    @Deprecated
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
    @Deprecated
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
    @Deprecated
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
    @Deprecated
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
    @Deprecated
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
    @Deprecated
    public void clear() {
        throw new UnsupportedOperationException(
                "'removeAll' called on immutable set!");
    }

    /**
     * Returns a new immutable set that contains all elements of
     * <code>this</code> set, plus the given <code>element</code>.
     * <code>this</code> set is not altered.
     * 
     * @param element
     * @return <code>this</code> union <code>element</code>.
     */
    public ImmutableHashSet<E> addToCopy(E element) {
        Set<E> tmp = new HashSet<E>(internalSet);
        tmp.add(element);
        return new ImmutableHashSet<E>(tmp);
    }

    /**
     * Returns a new immutable set that contains all elements of
     * <code>this</code> set, plus the given <code>set</code>. <code>this</code>
     * set is not altered.
     * 
     * @param set
     * @return <code>this</code> union <code>set</code>.
     */
    public ImmutableHashSet<E> addAllToCopy(Collection<? extends E> set) {
        if (set == null)
            return this;
        Set<E> tmp = new HashSet<E>(internalSet);
        tmp.addAll(set);
        return new  ImmutableHashSet<E>(tmp);
    }

    /**
     * Returns a new immutable set that contains all elements of
     * <code>this</code> set, minus the given <code>element</code>.
     * <code>this</code> set is not altered. If <code>element</code> is not in
     * <code>this</code> set, then a copy of <code>this</code> set is returned.
     * 
     * @param element
     * @return <code>this</code> union <code>element</code>.
     */
    public ImmutableHashSet<E> removeFromCopy(E element) {
        Set<E> tmp = new HashSet<E>(internalSet);
        tmp.remove(element);
        return new ImmutableHashSet<E>(tmp);
    }

    /**
     * Returns a new immutable set that contains all elements of
     * <code>this</code> set, minus the given <code>set</code>.
     * <code>this</code> set is not altered. Any elements of <code>set</code>
     * not contained in <code>this</code> are basically ignored.
     * 
     * @param set
     * @return <code>this</code> union <code>set</code>.
     */
    public ImmutableHashSet<E> removeAllFromCopy(Collection<? extends E> set) {
        if (set == null)
            return this;
        Set<E> tmp = new HashSet<E>(internalSet);
        tmp.removeAll(set);
        return new ImmutableHashSet<E>(tmp);
    }

    @Override
    public String toString() {
        return internalSet.toString();
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return hashCode;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof Set))
            return false;
        if (this.hashCode != obj.hashCode())
            return false;

        return internalSet.equals(obj);
    }

}
