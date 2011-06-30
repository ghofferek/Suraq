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
import at.iaik.suraq.formula.FunctionMacroInstance;
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
        LogicParser logicParser = null;
        try {
            SExpParser sexpParser = new SExpParser(new File(
                    "./rsc/test/no_readonly_pipeline_example_suraq.smt2"));
            sexpParser.parse();
            Assert.assertTrue(sexpParser.wasParsingSuccessfull());
            SExpression result = sexpParser.getRootExpr();
            Assert.assertNotNull(result);

            logicParser = new LogicParser(result);
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

        // Some more detailed checks

        Assert.assertEquals(1, logicParser.getControlVariables().size());
        Assert.assertEquals("x", logicParser.getControlVariables().get(0)
                .getVarName());
        Assert.assertEquals(1, logicParser.getFunctions().size());
        Assert.assertEquals("ALU", logicParser.getFunctions().get(0).getName()
                .toString());
        Assert.assertEquals(0, logicParser.getBoolVariables().size());
        Assert.assertEquals(3, logicParser.getMacros().size());
        Assert.assertEquals(5, logicParser.getArrayVariables().size());
        Assert.assertEquals(5, logicParser.getDomainVariables().size());
        Assert.assertEquals(5, logicParser.getNoDependenceVariables().size());

        Assert.assertNotNull(logicParser.getMainFormula());
        Assert.assertTrue(logicParser.getMainFormula() instanceof FunctionMacroInstance);

    }
}
