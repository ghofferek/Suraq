/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.parser.SExpParser;
import at.iaik.suraq.sexp.SExpression;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class SExpParserTest {

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#getSourceLines()}.
     */
    @Test
    public void testGetSourceLinesNull() {
        SExpParser parser = new SExpParser((String) null);
        String[] expected = { "" };
        Assert.assertArrayEquals(expected, parser.getSourceLines());
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#getSourceLines()}.
     */
    @Test
    public void testGetSourceLinesEmpty() {
        SExpParser parser = new SExpParser("");
        String[] expected = { "" };
        Assert.assertArrayEquals(expected, parser.getSourceLines());
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#getSourceLines()}.
     */
    @Test
    public void testGetSourceLinesOneLine() {
        String testString = "This is just some test string.";
        SExpParser parser = new SExpParser(testString);
        String[] expected = { testString };
        Assert.assertArrayEquals(expected, parser.getSourceLines());
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#getSourceLines()}.
     */
    @Test
    public void testGetSourceLinesTwoLines() {
        String testString = "This is just some test string.\nWith two lines";
        SExpParser parser = new SExpParser(testString);
        String[] expected = testString.split("\n");
        Assert.assertArrayEquals(expected, parser.getSourceLines());
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParseEmpty() {
        SExpParser parser = new SExpParser("");
        try {
            parser.parse();
            Assert.assertTrue(parser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            exc.printStackTrace();
            Assert.fail(exc.getMessage());
        }
        SExpression result = parser.getRootExpr();
        Assert.assertNotNull(result);
        Assert.assertTrue(result.size() == 0);
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParseSpace() {
        SExpParser parser = new SExpParser(" ");
        try {
            parser.parse();
            Assert.assertTrue(parser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            exc.printStackTrace();
            Assert.fail(exc.getMessage());
        }
        SExpression result = parser.getRootExpr();
        Assert.assertNotNull(result);
        Assert.assertTrue(result.size() == 0);
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParseWitespace() {
        SExpParser parser = new SExpParser("      \n   \r    \t  \n");
        try {
            parser.parse();
            Assert.assertTrue(parser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            exc.printStackTrace();
            Assert.fail(exc.getMessage());
        }
        SExpression result = parser.getRootExpr();
        Assert.assertNotNull(result);
        Assert.assertTrue(result.size() == 0);
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParseComment() {
        SExpParser parser = new SExpParser(
                "   ; This is a comment\n   \n  \t  ; and another one");
        try {
            parser.parse();
            Assert.assertTrue(parser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            exc.printStackTrace();
            Assert.fail(exc.getMessage());
        }
        SExpression result = parser.getRootExpr();
        Assert.assertNotNull(result);
        Assert.assertTrue(result.size() == 0);
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParseSingleToken() {
        SExpParser parser = new SExpParser("SingleToken");
        try {
            parser.parse();
            Assert.assertTrue(parser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            exc.printStackTrace();
            Assert.fail(exc.getMessage());
        }
        SExpression result = parser.getRootExpr();
        Assert.assertNotNull(result);
        Assert.assertTrue(result.size() == 1);
        Assert.assertEquals(result.getChildren().get(0).toString(),
                "SingleToken");
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParseSingleTokenAndWhitespace() {
        SExpParser parser = new SExpParser("  SingleToken \n   \t \r");
        try {
            parser.parse();
            Assert.assertTrue(parser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            exc.printStackTrace();
            Assert.fail(exc.getMessage());
        }
        SExpression result = parser.getRootExpr();
        Assert.assertNotNull(result);
        Assert.assertEquals(1, result.size());
        Assert.assertEquals(result.getChildren().get(0).toString(),
                "SingleToken");
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParseSingleTokenAndWhitespaceAndComments() {
        SExpParser parser = new SExpParser(
                "  ; a comment\nSingleToken ;another comment\n  ; comment \t \r");
        try {
            parser.parse();
            Assert.assertTrue(parser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            exc.printStackTrace();
            Assert.fail(exc.getMessage());
        }
        SExpression result = parser.getRootExpr();
        Assert.assertNotNull(result);
        Assert.assertEquals(1, result.size());
        Assert.assertEquals(result.getChildren().get(0).toString(),
                "SingleToken");
    }

    /**
     * Test method for
     * {@link at.iaik.suraq.parser.SExpParser#wasParsingSuccessfull()}.
     */
    @Test
    public void testWasParsingSuccessfull() {
        SExpParser parser = new SExpParser("");
        Assert.assertFalse(parser.wasParsingSuccessfull());
        try {
            parser.parse();
        } catch (ParseError exc) {
            exc.printStackTrace();
            Assert.fail(exc.getMessage());
        }
        Assert.assertTrue(parser.wasParsingSuccessfull());
    }

}
