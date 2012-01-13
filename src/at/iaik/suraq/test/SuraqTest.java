/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.main.Suraq;

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
}
