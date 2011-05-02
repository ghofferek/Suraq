/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class SExpressionTest {

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpression#toString()}.
     */
    @Test
    public void testToString() {
        SExpression expr = new SExpression();
        Token first = new Token("first");
        Token second = new Token("second");
        Token third = new Token("third");
        SExpression secondThird = new SExpression();
        secondThird.addChild(second);
        secondThird.addChild(third);
        expr.addChild(first);
        expr.addChild(secondThird);
        String expected = "(\n  first\n  (\n    second\n    third\n  )\n)\n";
        String actual = expr.toString();
        Assert.assertEquals(expected, actual);
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpression#equals()}.
     */
    @Test
    public void testEquals() {
        SExpression expr = new SExpression();
        Token first = new Token("first");
        Token second = new Token("second");
        Token third = new Token("third");
        SExpression secondThird = new SExpression();
        secondThird.addChild(second);
        secondThird.addChild(third);
        expr.addChild(first);
        expr.addChild(secondThird);
        Assert.assertFalse(second.equals(third));
        Assert.assertFalse(third.equals(second));
        Assert.assertFalse(first.equals(second));
        Assert.assertFalse(expr.equals(secondThird));
        Assert.assertTrue(expr.equals(expr.deepCopy()));
    }
}
