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
     * Lets Suraq run on the simple_2_controllers.smt2. Just checks that there
     * are no exceptions and that the program terminates normally. No functional
     * correctness is tested.
     */
    @Test
    public void simpleRunOnSimple2ControllersExample() {
        String[] args = { "-i", "./rsc/test/simple_2_controllers.smt2", "-s",
                "./rsc/test/suraq_out_simple_2_controllers.smt2" };
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
        String[] args = { "-i", "./rsc/dlx/dlx_no_domainITE.smt2", "-s",
                "./rsc/dlx/suraq_out_dlx.smt2" };
        Suraq suraq = new Suraq(args);
        suraq.run();
        Assert.assertTrue(suraq.success());
    }

    /**
     * Lets Suraq run on the DLX example, with just control signals for operand
     * a. Just checks that there are no exceptions and that the program
     * terminates normally. No functional correctness is tested.
     */
    @Test
    public void simpleRunOnDLXOnlyAExample() {
        String[] args = { "-i",
                "./rsc/dlx/dlx_no_domainITE_control_a_only.smt2", "-s",
                "./rsc/dlx/suraq_out_dlx_control_a_only.smt2" };
        Suraq suraq = new Suraq(args);
        suraq.run();
        Assert.assertTrue(suraq.success());
    }

    /**
     * Lets Suraq run on the DLX example, with just control signals for operand
     * b. Just checks that there are no exceptions and that the program
     * terminates normally. No functional correctness is tested.
     */
    @Test
    public void simpleRunOnDLXOnlyBExample() {
        String[] args = { "-i",
                "./rsc/dlx/dlx_no_domainITE_control_b_only.smt2", "-s",
                "./rsc/dlx/suraq_out_dlx_control_b_only.smt2" };
        Suraq suraq = new Suraq(args);
        suraq.run();
        Assert.assertTrue(suraq.success());
    }

    /**
     * Lets Suraq run on the DLX example, with just control signals for operand
     * a and stall. Just checks that there are no exceptions and that the
     * program terminates normally. No functional correctness is tested.
     */
    @Test
    public void simpleRunOnDLXAAndStallExample() {
        String[] args = { "-i", "./rsc/dlx/dlx_no_domainITE_a_and_stall.smt2",
                "-s", "./rsc/dlx/suraq_out_dlx_control_a_and_stall.smt2" };
        Suraq suraq = new Suraq(args);
        suraq.run();
        Assert.assertTrue(suraq.success());
    }

    /**
     * Lets Suraq run on the DLX example, with just control signals for operand
     * b and stall. Just checks that there are no exceptions and that the
     * program terminates normally. No functional correctness is tested.
     */
    @Test
    public void simpleRunOnDLXBAndStallExample() {
        String[] args = { "-i", "./rsc/dlx/dlx_no_domainITE_b_and_stall.smt2",
                "-s", "./rsc/dlx/suraq_out_dlx_control_b_and_stall.smt2" };
        Suraq suraq = new Suraq(args);
        suraq.run();
        Assert.assertTrue(suraq.success());
    }

    /**
     * Lets Suraq run on the DLX example, with control signals for operands a
     * and b. Just checks that there are no exceptions and that the program
     * terminates normally. No functional correctness is tested.
     */
    @Test
    public void simpleRunOnDLXAAndBExample() {
        String[] args = { "-i",
                "./rsc/dlx/dlx_no_domainITE_control_a_and_b.smt2", "-s",
                "./rsc/dlx/suraq_out_dlx_control_a_and_b.smt2" };
        Suraq suraq = new Suraq(args);
        suraq.run();
        Assert.assertTrue(suraq.success());
    }

    /**
     * Lets Suraq run on the DLX example, with just control signals for
     * forwarding from EX stage. Just checks that there are no exceptions and
     * that the program terminates normally. No functional correctness is
     * tested.
     */
    @Test
    public void simpleRunOnDLX2ControllersExample() {
        String[] args = { "-i",
                "./rsc/dlx/dlx_no_domainITE_2_controllers.smt2", "-s",
                "./rsc/dlx/suraq_out_dlx_2_controllers.smt2" };
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
