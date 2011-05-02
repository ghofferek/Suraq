/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.parser.SExpParser;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

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
                "SingleToken\n");
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
                "SingleToken\n");
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
                "SingleToken\n");
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParseThreeTokensAndComments() {
        SExpParser parser = new SExpParser(
                "  ; a comment\nFirstToken ;another comment\n\n\t   SecondToken ThirdToken  ; comment \t \r");
        try {
            parser.parse();
            Assert.assertTrue(parser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            exc.printStackTrace();
            Assert.fail(exc.getMessage());
        }
        SExpression result = parser.getRootExpr();
        Assert.assertNotNull(result);
        Assert.assertEquals(3, result.size());
        Assert.assertEquals("FirstToken\n", result.getChildren().get(0)
                .toString());
        Assert.assertEquals("SecondToken\n", result.getChildren().get(1)
                .toString());
        Assert.assertEquals("ThirdToken\n", result.getChildren().get(2)
                .toString());
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParseEmpytExpression() {
        SExpParser parser = new SExpParser("()");
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
        Assert.assertEquals(0, result.getChildren().get(0).size());
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParseEmpytExpressionNested() {
        SExpParser parser = new SExpParser("(())");
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
        Assert.assertEquals(1, result.getChildren().get(0).size());
        Assert.assertEquals(0, result.getChildren().get(0).getChildren().get(0)
                .size());
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParseNestedExpression() {
        SExpParser parser;
        try {
            parser = new SExpParser("(first (second third))");
            parser.parse();
            Assert.assertTrue(parser.wasParsingSuccessfull());
            SExpression result = parser.getRootExpr();
            Assert.assertNotNull(result);
            Token first = new Token("first");
            Token second = new Token("second");
            Token third = new Token("third");
            SExpression secondThird = new SExpression();
            secondThird.addChild(second);
            secondThird.addChild(third);
            SExpression expected = new SExpression();
            expected.addChild(first);
            expected.addChild(secondThird);
            Assert.assertTrue(result.size() == 1);
            Assert.assertEquals(expected, result.getChildren().get(0));
        } catch (ParseError exc) {
            exc.printStackTrace();
            Assert.fail(exc.getMessage());
        }
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParsePipelineExample() {
        SExpParser parser;
        try {
            parser = new SExpParser(new File(
                    "./rsc/test/no_readonly_pipeline_example.smt2"));
            parser.parse();
            Assert.assertTrue(parser.wasParsingSuccessfull());
            SExpression result = parser.getRootExpr();
            Assert.assertNotNull(result);
            SExpression actualFirst = result.getChildren().get(0);
            SExpression[] expectedFirstChildren = { new Token("set-logic"),
                    new Token("ArraysEx") };
            SExpression expectedFirst = new SExpression(expectedFirstChildren);
            SExpression actualLast = result.getChildren().get(
                    result.getChildren().size() - 1);
            SExpression[] expectedLastChildren = { new Token("get-info"),
                    new Token("model") };
            SExpression expectedLast = new SExpression(expectedLastChildren);
            Assert.assertEquals(expectedFirst, actualFirst);
            Assert.assertEquals(expectedLast, actualLast);
        } catch (FileNotFoundException exc1) {
            exc1.printStackTrace();
            Assert.fail(exc1.getMessage());
        } catch (IOException exc1) {
            exc1.printStackTrace();
            Assert.fail(exc1.getMessage());
        } catch (ParseError exc) {
            exc.printStackTrace();
            Assert.fail(exc.getMessage());
        }
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParsePipelineExampleUIFE() {
        SExpParser parser;
        try {
            parser = new SExpParser(new File(
                    "./rsc/test/no_readonly_pipeline_example_uife.smt2"));
            parser.parse();
            Assert.assertTrue(parser.wasParsingSuccessfull());
            SExpression result = parser.getRootExpr();
            Assert.assertNotNull(result);
            SExpression actualFirst = result.getChildren().get(0);
            SExpression[] expectedFirstChildren = { new Token("set-logic"),
                    new Token("QF_LIA") };
            SExpression expectedFirst = new SExpression(expectedFirstChildren);
            SExpression actualLast = result.getChildren().get(
                    result.getChildren().size() - 1);
            SExpression[] expectedLastChildren = { new Token("check-sat") };
            SExpression expectedLast = new SExpression(expectedLastChildren);
            Assert.assertEquals(expectedFirst, actualFirst);
            Assert.assertEquals(expectedLast, actualLast);
            Assert.assertEquals(
                    result.getChildren().get(result.getChildren().size() - 2)
                            .getChildren().get(0), new Token("assert"));
        } catch (FileNotFoundException exc1) {
            exc1.printStackTrace();
            Assert.fail(exc1.getMessage());
        } catch (IOException exc1) {
            exc1.printStackTrace();
            Assert.fail(exc1.getMessage());
        } catch (ParseError exc) {
            exc.printStackTrace();
            Assert.fail(exc.getMessage());
        }
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParsePipelineExampleEQ() {
        SExpParser parser;
        try {
            parser = new SExpParser(new File(
                    "./rsc/test/no_readonly_pipeline_example_eq.smt2"));
            parser.parse();
            Assert.assertTrue(parser.wasParsingSuccessfull());
            SExpression result = parser.getRootExpr();
            Assert.assertNotNull(result);
            SExpression actualFirst = result.getChildren().get(0);
            SExpression[] expectedFirstChildren = { new Token("set-logic"),
                    new Token("QF_LIA") };
            SExpression expectedFirst = new SExpression(expectedFirstChildren);
            SExpression actualLast = result.getChildren().get(
                    result.getChildren().size() - 1);
            SExpression[] expectedLastChildren = { new Token("check-sat") };
            SExpression expectedLast = new SExpression(expectedLastChildren);
            Assert.assertEquals(expectedFirst, actualFirst);
            Assert.assertEquals(expectedLast, actualLast);
            Assert.assertEquals(
                    result.getChildren().get(result.getChildren().size() - 2)
                            .getChildren().get(0), new Token("assert"));
        } catch (FileNotFoundException exc1) {
            exc1.printStackTrace();
            Assert.fail(exc1.getMessage());
        } catch (IOException exc1) {
            exc1.printStackTrace();
            Assert.fail(exc1.getMessage());
        } catch (ParseError exc) {
            exc.printStackTrace();
            Assert.fail(exc.getMessage());
        }
    }

    /**
     * Test method for {@link at.iaik.suraq.parser.SExpParser#parse()}.
     */
    @Test
    public void testParsePipelineExampleProp() {
        SExpParser parser;
        try {
            parser = new SExpParser(new File(
                    "./rsc/test/no_readonly_pipeline_example_prop.smt2"));
            parser.parse();
            Assert.assertTrue(parser.wasParsingSuccessfull());
            SExpression result = parser.getRootExpr();
            Assert.assertNotNull(result);
            SExpression actualFirst = result.getChildren().get(0);
            SExpression[] expectedFirstChildren = { new Token("set-option"),
                    new Token(":print-success"), new Token("false") };
            SExpression expectedFirst = new SExpression(expectedFirstChildren);
            SExpression actualLast = result.getChildren().get(
                    result.getChildren().size() - 1);
            SExpression[] expectedLastChildren = { new Token("check-sat") };
            SExpression expectedLast = new SExpression(expectedLastChildren);
            Assert.assertEquals(expectedFirst, actualFirst);
            Assert.assertEquals(expectedLast, actualLast);
            Assert.assertEquals(
                    result.getChildren().get(result.getChildren().size() - 2)
                            .getChildren().get(0), new Token("assert"));
        } catch (FileNotFoundException exc1) {
            exc1.printStackTrace();
            Assert.fail(exc1.getMessage());
        } catch (IOException exc1) {
            exc1.printStackTrace();
            Assert.fail(exc1.getMessage());
        } catch (ParseError exc) {
            exc.printStackTrace();
            Assert.fail(exc.getMessage());
        }
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
