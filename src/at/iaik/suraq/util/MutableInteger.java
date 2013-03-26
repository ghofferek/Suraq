/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

/**
 * 
 * A class for passing (mutable) integers by reference.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class MutableInteger {
    /**
     * The actual value of this instance.
     */
    private int value;

    public MutableInteger(int value) {
        this.value = value;
    }

    public MutableInteger(Integer value) {
        this.value = value.intValue();
    }

    public MutableInteger(MutableInteger value) {
        this.value = value.value;
    }

    public int intValue() {
        return value;
    }

    public Integer toInteger() {
        return value;
    }

    public void setValue(int newValue) {
        value = newValue;
    }

    public void add(int value) {
        this.value += value;
    }

    public void subtract(int value) {
        this.value -= value;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return value;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof MutableInteger))
            return false;
        return this.value == ((MutableInteger) obj).value;
    }

    /**
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return Integer.toString(value);
    }

}
