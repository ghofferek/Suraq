/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.ArrayList;

/**
 * A stack based on an array list.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class Stack<E> {

    /**
     * The elements of the stack.
     */
    private final ArrayList<E> elements = new ArrayList<E>();

    /**
     * 
     * @return the size of the stack
     */
    public int size() {
        return elements.size();
    }

    /**
     * 
     * @return <code>true</code> if the stack is empty.
     */
    public boolean isEmpty() {
        return elements.isEmpty();
    }

    /**
     * Pushes the given element on the stack
     * 
     * @param e
     *            the element to push
     */
    public void push(E e) {
        if (e == null)
            throw new NullPointerException();
        elements.add(e);
    }

    /**
     * Pops the last element from the stack.
     * 
     * @return the last element put onto the stack, or <code>null</code> if the
     *         stack is empty.
     */
    public E pop() {
        if (elements.isEmpty())
            return null;
        else {
            E result = elements.get(elements.size() - 1);
            elements.remove(elements.size() - 1);
            return result;
        }
    }

    /**
     * Returns the last element of the stack without popping it.
     * 
     * @return the last element put onto the stack, or <code>null</code> if the
     *         stack is empty.
     */
    public E peek() {
        return elements.isEmpty() ? null : elements.get(elements.size() - 1);
    }

    /**
     * 
     * @param element
     * @return <code>true</code> if the stack contains the given element.
     */
    public boolean contains(E element) {
        return elements.contains(element);
    }
}
