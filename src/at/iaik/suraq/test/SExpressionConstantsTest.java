/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import java.lang.reflect.Field;

import org.junit.Assert;
import org.junit.Test;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class SExpressionConstantsTest {
    /**
     * Tests that all static s-expression constants are non-null
     */
    @Test
    public void testConstants() {
        String className = "at.iaik.suraq.sexp.SExpressionConstants";
        Class<?> classObject = null;
        try {
            classObject = Class.forName(className);

        } catch (ClassNotFoundException exc) {
            exc.printStackTrace();
            Assert.fail();
        }
        Assert.assertTrue(classObject != null);
        Assert.assertTrue(classObject.getName().equals(className));

        for (Field field : classObject.getFields()) {
            try {
                Assert.assertTrue(field.get(classObject.newInstance()) != null);
            } catch (IllegalArgumentException exc) {
                exc.printStackTrace();
                Assert.fail();
            } catch (IllegalAccessException exc) {
                exc.printStackTrace();
                Assert.fail();
            } catch (InstantiationException exc) {
                exc.printStackTrace();
                Assert.fail();
            }
        }
    }
}
