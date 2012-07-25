/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.io.Serializable;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ImmutableSet<E> implements Set<E>, Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = 8782268576752007761L;

    private final Set<E> internalSet;

    private int hashCode;

    private static Map<Set<?>, ImmutableSet<?>> instances = new WeakHashMap<Set<?>, ImmutableSet<?>>();

    private static Map<Object, Object> uniqueElements = new WeakHashMap<Object, Object>();

    /**
     * Constructs a new <code>ImmutableSet</code>.
     * 
     * @param set
     */
    private ImmutableSet(Collection<? extends E> set) {

        assert (set != null);
        internalSet = new HashSet<E>();

        for (E element : set) {
            if (element == null) {
                internalSet.add(null);
            } else {
                assert (element != null);
                @SuppressWarnings("unchecked")
                E uniqueElement = (E) ImmutableSet.uniqueElements.get(element);
                if (uniqueElement != null)
                    internalSet.add(uniqueElement);
                else {
                    ImmutableSet.uniqueElements.put(element, element);
                    internalSet.add(element);
                }
            }
        }

        Set<E> key = new HashSet<E>();
        key.addAll(set);
        ImmutableSet.instances.put(key, this);

        this.hashCode = internalSet.hashCode();
    }

    public static <T> ImmutableSet<T> create(Collection<? extends T> set) {

        if (set == null)
            throw new NullPointerException(
                    "Cannot create ImmutableSet from null.");

        ImmutableSet<?> existingSet = ImmutableSet.instances.get(set);
        if (existingSet != null) {

            if (set.isEmpty()) {
                assert (existingSet.isEmpty());
                ImmutableSet<?> tmp = existingSet;
                assert (tmp.isEmpty());
                @SuppressWarnings("unchecked")
                ImmutableSet<T> castResult = (ImmutableSet<T>) tmp;
                return castResult;
            }

            assert (!set.isEmpty());
            assert (!existingSet.isEmpty());
            assert (existingSet.iterator().next().getClass().isInstance(set
                    .iterator().next()));
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
    public ImmutableSet<E> addToCopy(E element) {
        Set<E> tmp = new HashSet<E>();
        tmp.addAll(internalSet);
        tmp.add(element);
        return ImmutableSet.create(tmp);
    }

    /**
     * Returns a new immutable set that contains all elements of
     * <code>this</code> set, plus the given <code>set</code>. <code>this</code>
     * set is not altered.
     * 
     * @param set
     * @return <code>this</code> union <code>set</code>.
     */
    public ImmutableSet<E> addAllToCopy(Collection<? extends E> set) {
        if (set == null)
            return this;
        Set<E> tmp = new HashSet<E>();
        tmp.addAll(internalSet);
        tmp.addAll(set);
        return ImmutableSet.create(tmp);
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
    public ImmutableSet<E> removeFromCopy(E element) {
        Set<E> tmp = new HashSet<E>();
        tmp.addAll(internalSet);
        tmp.remove(element);
        return ImmutableSet.create(tmp);
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
    public ImmutableSet<E> removeAllFromCopy(Collection<? extends E> set) {
        if (set == null)
            return this;
        Set<E> tmp = new HashSet<E>();
        tmp.addAll(internalSet);
        tmp.removeAll(set);
        return ImmutableSet.create(tmp);
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

    /**
     * @return the <code>instances</code>
     */
    public static Map<Set<?>, ImmutableSet<?>> getInstances() {
        return ImmutableSet.instances;
    }

    /**
     * Necessary for restore after load from cache. Do not tamper with the
     * instances otherwise!
     * 
     * @param <code>instances</code> the new value for <code>instances</code>
     */
    public static void setInstances(Map<Set<?>, ImmutableSet<?>> instances) {
        ImmutableSet.instances = instances;
    }

    /**
     * @return the <code>uniqueElements</code>
     */
    public static Map<Object, Object> getUniqueElements() {
        return ImmutableSet.uniqueElements;
    }

    /**
     * Necessary for restore after load from cache. Do not tamper with the
     * unique elements otherwise!
     * 
     * @param <code>uniqueElements</code> the new value for
     *        <code>uniqueElements</code>
     */
    public static void setUniqueElements(Map<Object, Object> uniqueElements) {
        ImmutableSet.uniqueElements = uniqueElements;
    }

}
