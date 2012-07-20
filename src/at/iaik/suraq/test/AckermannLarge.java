package at.iaik.suraq.test;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import at.iaik.suraq.main.Ackermann;
import at.iaik.suraq.main.GraphReduction;
import at.iaik.suraq.main.Suraq;
import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.smtlib.Z3Proof;

public class AckermannLarge {

    @Before
    public void setUp() {
        SuraqOptions.kill();
        SuraqOptions.reset();
        Z3Proof.setInstanceCounter(0);
    }

    

    @Test
    public void performFullSuraq2_simple_3_input_dependent_2_controllers() { 
        System.out.println("****************************************************");
        
        // change only this parameter for testing without ackermann
        // the output file will differ in both cases
        // the algorithm will be deactivated automatically.
        boolean ackermannActive = true;
        
        String testfilename = null;
        if(ackermannActive)
            //testfilename = "./rsc/dlx/dlx_small.smt2";
            testfilename = "./rsc/dlx/dlx_no_domainITE_2_controllers.smt2";
        else
            testfilename = "./rsc/dlx/dlx_small.smt2";
            //testfilename = "./rsc/dlx/dlx_no_domainITE_2_controllers-noackermann.smt2";
        Ackermann.setActive(ackermannActive);
        Ackermann.setFunctionActive(true);
        Ackermann.setPredicateActive(true);
        
        GraphReduction.setActive(false);
        
        String[] args = { "-i", testfilename }; //, "-v", "--check-result"
        Suraq suraq = new Suraq(args);
        suraq.run();
        Assert.assertTrue(suraq.success());
    }
    
}
