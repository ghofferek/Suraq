/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

/**
 * 
 * Generates unique IDs for (other) objects.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class IdGenerator {

    private static long id = 0;

    public static synchronized long getId() {
        return IdGenerator.id++;
    }

}
