/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import org.junit.After;
import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.main.Suraq;
import at.iaik.suraq.main.SuraqOptions;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class SuraqTest {

    /**
     * Lets Suraq run on the no_readonly_pipeline_example. Just checks that
     * there are no exceptions and that the program terminates normally. No
     * functional correctness is tested.
     */
    @Test
    public void simpleRunOnNoReadonlyPipelineExample() {
        String[] args = { "-i",
                "./rsc/test/no_readonly_pipeline_example_suraq.smt2", "-s",
                "./rsc/test/suraq_out.smt2" };
        Suraq suraq = new Suraq(args);
        suraq.run();
        Assert.assertTrue(suraq.success());
    }

    /**
     * Lets Suraq run on the DLX example. Just checks that there are no
     * exceptions and that the program terminates normally. No functional
     * correctness is tested.
     */
    @Test
    public void simpleRunOnDLXExample() {
        String[] args = { "-i", "./rsc/dlx/dlx.smt2", "-s",
                "./rsc/dlx/suraq_out.smt2" };
        Suraq suraq = new Suraq(args);
        suraq.run();
        Assert.assertTrue(suraq.success());
    }

    /**
     * Deletes the <code>SuraqOptions</code>.
     * 
     * @throws Exception
     */
    @After
    public void tearDown() throws Exception {
        SuraqOptions.kill();
    }
}
