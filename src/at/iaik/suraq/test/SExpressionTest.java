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
        Token first = Token.generate("first");
        Token second = Token.generate("second");
        Token third = Token.generate("third");
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
     * Test method for {@link at.iaik.suraq.parser.SExpression#toString()}.
     */
    @Test
    public void testToStringConstants1() {
        String expressionString = "(set-logic QF_UF)";
        SExpression expr = SExpression.fromString(expressionString);
        String actual = expr.toString();
        Assert.assertEquals(expressionString.replaceAll("\\s", ""),
                actual.replaceAll("\\s", ""));
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpression#toString()}.
     */
    @Test
    public void testToStringConstants2() {
        String expressionString = "(define-fun equiv ((A (Array Value Value))(B (Array Value Value))) Bool (  forall ((i Value)) (    = (select A i)      (select B i)    )))";
        SExpression expr = SExpression.fromString(expressionString);
        String actual = expr.toString();
        Assert.assertEquals(expressionString.replaceAll("\\s", ""),
                actual.replaceAll("\\s", ""));
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpression#toString()}.
     */
    @Test
    public void testToStringConstants3() {
        String expressionString = "(declare-fun REGci_   () (Array Value Value) :no_dependence)";
        SExpression expr = SExpression.fromString(expressionString);
        String actual = expr.toString();
        Assert.assertEquals(expressionString.replaceAll("\\s", ""),
                actual.replaceAll("\\s", ""));
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpression#toString()}.
     */
    @Test
    public void testToStringConstants4() {
        String expressionString = "(exit)";
        SExpression expr = SExpression.fromString(expressionString);
        String actual = expr.toString();
        Assert.assertEquals(expressionString.replaceAll("\\s", ""),
                actual.replaceAll("\\s", ""));
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpression#equals()}.
     */
    @Test
    public void testEquals() {
        SExpression expr = new SExpression();
        Token first = Token.generate("first");
        Token second = Token.generate("second");
        Token third = Token.generate("third");
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
