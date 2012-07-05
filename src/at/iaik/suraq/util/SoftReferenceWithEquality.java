/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.lang.ref.SoftReference;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class SoftReferenceWithEquality<T> extends SoftReference<T> {

    /**
     * Constructs a new <code>SoftReferenceWithEquality</code>.
     */
    public SoftReferenceWithEquality(T obj) {
        super(obj);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return this.get() == null ? 0 : this.get().hashCode();
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {

        return this.get() == null ? obj == null : this.get().equals(obj);
    }

}
