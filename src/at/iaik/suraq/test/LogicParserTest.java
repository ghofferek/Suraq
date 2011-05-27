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
import at.iaik.suraq.parser.LogicParser;
import at.iaik.suraq.parser.SExpParser;
import at.iaik.suraq.sexp.SExpression;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class LogicParserTest {
    /**
     * Test method for {@link at.iaik.suraq.parser.LogicParser#parse()}.
     */
    @Test
    public void testParseNoReadonlyPipelineExample() {

        try {
            SExpParser sexpParser = new SExpParser(new File(
                    "./rsc/test/no_readonly_pipeline_example_suraq.smt2"));
            sexpParser.parse();
            Assert.assertTrue(sexpParser.wasParsingSuccessfull());
            SExpression result = sexpParser.getRootExpr();
            Assert.assertNotNull(result);

            LogicParser logicParser = new LogicParser(result);
            logicParser.parse();
            Assert.assertTrue(logicParser.wasParsingSuccessfull());

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
}
