/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.parser.SExpParser;

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
    public void testParse() {
        Assert.fail("Not yet implemented");
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
