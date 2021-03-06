/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.smtlib.formula.Term;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TermTest {
    /**
     * Tests that all static <code>Class</code> constants have the correct
     * value.
     * 
     * @throws ClassNotFoundException
     */
    @Test
    public void testConstants() throws ClassNotFoundException {

        Assert.assertEquals(
                Class.forName("at.iaik.suraq.smtlib.formula.DomainTerm"),
                Term.domainTermClass);
        Assert.assertEquals(
                Class.forName("at.iaik.suraq.smtlib.formula.ArrayTerm"),
                Term.arrayTermClass);
        Assert.assertEquals(
                Class.forName("at.iaik.suraq.smtlib.formula.PropositionalTerm"),
                Term.propositionalTermClass);
    }
}
