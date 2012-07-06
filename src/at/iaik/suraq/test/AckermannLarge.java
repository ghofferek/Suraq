package at.iaik.suraq.test;

import static org.junit.Assert.*;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

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
        
        String[] args = { "-i",
        "./rsc/dlx/dlx_no_domainITE_2_controllers.smt2"}; //, "-v", "--check-result"
        Suraq suraq = new Suraq(args);
        suraq.run();
        Assert.assertTrue(suraq.success());
    }
    
}
