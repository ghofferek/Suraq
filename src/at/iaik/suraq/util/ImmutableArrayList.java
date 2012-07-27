/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.util;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

/**
 * @author Christoph Hillebold <c.hillebold@student.tugraz.at>
 * 
 */
public class ImmutableArrayList<E> implements List<E>, Serializable {

    private static final long serialVersionUID = 8782268576752007764L;
    private final ArrayList<E> internalSet;
    private final int hashCode;

    /**
     * Constructs a new <code>ImmutableSet</code>.
     * 
     * @param set
     */
    public ImmutableArrayList(List<? extends E> set) {
        assert (set != null);
        internalSet = new ArrayList<E>(set);
        this.hashCode = internalSet.hashCode();
    }
    

    public ImmutableArrayList(Collection<? extends E> set) {
        assert (set != null);
        internalSet = new ArrayList<E>(set);
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
                "'add' called on immutable list!");
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
                "'remove' called on immutable list!");
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
                "'addAll' called on immutable list!");
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
                "'retainAll' called on immutable list!");
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
                "'removeAll' called on immutable list!");
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
                "'removeAll' called on immutable list!");
    }

    /**
     * Returns a new immutable set that contains all elements of
     * <code>this</code> set, plus the given <code>element</code>.
     * <code>this</code> set is not altered.
     * 
     * @param element
     * @return <code>this</code> union <code>element</code>.
     */
    public ImmutableArrayList<E> addToCopy(E element) {
        ArrayList<E> tmp = new ArrayList<E>(internalSet);
        tmp.add(element);
        return new ImmutableArrayList<E>(tmp);
    }

    /**
     * Returns a new immutable set that contains all elements of
     * <code>this</code> set, plus the given <code>set</code>. <code>this</code>
     * set is not altered.
     * 
     * @param set
     * @return <code>this</code> union <code>set</code>.
     */
    public ImmutableArrayList<E> addAllToCopy(Collection<? extends E> set) {
        if (set == null)
            return this;
        ArrayList<E> tmp = new ArrayList<E>(internalSet);
        tmp.addAll(set);
        return new  ImmutableArrayList<E>(tmp);
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
    public ImmutableArrayList<E> removeFromCopy(E element) {
        ArrayList<E> tmp = new ArrayList<E>(internalSet);
        tmp.remove(element);
        return new ImmutableArrayList<E>(tmp);
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
    public ImmutableArrayList<E> removeAllFromCopy(Collection<? extends E> set) {
        if (set == null)
            return this;
        ArrayList<E> tmp = new ArrayList<E>(internalSet);
        tmp.removeAll(set);
        return new ImmutableArrayList<E>(tmp);
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

    @Override
    @Deprecated
    public void add(int arg0, E arg1) {
        throw new UnsupportedOperationException(
                "'add' called on immutable list!");
        
    }

    @Override
    @Deprecated
    public boolean addAll(int arg0, Collection<? extends E> arg1) {
        throw new UnsupportedOperationException(
                "'addAll' called on immutable list!");
    }

    @Override
    public E get(int arg0) {
        return internalSet.get(arg0);
    }

    @Override
    public int indexOf(Object arg0) {
        return internalSet.indexOf(arg0);
    }

    @Override
    public int lastIndexOf(Object arg0) {
        return internalSet.lastIndexOf(arg0);
    }

    @Override
    public ListIterator<E> listIterator() {
        // TODO: make Immutableiterator
        return internalSet.listIterator();
    }

    @Override
    public ListIterator<E> listIterator(int arg0) {
        // TODO: make Immutableiterator
        return internalSet.listIterator(arg0);
    }

    @Override
    @Deprecated
    public E remove(int arg0) {
        throw new UnsupportedOperationException(
                "'remove' called on immutable list!");
    }

    @Override
    @Deprecated
    public E set(int arg0, E arg1) {
        throw new UnsupportedOperationException(
                "'set' called on immutable list!");
    }

    @Override
    public List<E> subList(int arg0, int arg1) {
        return new ImmutableArrayList<E>(internalSet.subList(arg0, arg1));
    }

}
