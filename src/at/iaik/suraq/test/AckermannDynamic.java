package at.iaik.suraq.test;

import java.io.BufferedReader;
import java.io.InputStreamReader;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import at.iaik.suraq.main.Ackermann;
import at.iaik.suraq.main.Suraq;
import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.smtlib.Z3Proof;

public class AckermannDynamic {

    @Before
    public void setUp() {
        SuraqOptions.kill();
        SuraqOptions.reset();
        Z3Proof.setInstanceCounter(0);
    }

    

    @Test
    public void performFullSuraq2_simple_3_input_dependent_2_controllers() throws Exception{ 
        System.out.println("****************************************************");
        
        // change only this parameter for testing without ackermann
        // the output file will differ in both cases
        // the algorithm will be deactivated automatically.
        boolean ackermannActive = true;
        
        BufferedReader sr = new BufferedReader(new InputStreamReader(System.in));
        System.out.println("Please enter an SMT2 input file (relative path: e.g. ./rsc/dlx/...)");
        String testfilename = sr.readLine();
        Ackermann.setActive(ackermannActive);
        
        String[] args = { "-i", testfilename }; //, "-v", "--check-result"
        Suraq suraq = new Suraq(args);
        suraq.run();
        Assert.assertTrue(suraq.success());
    }
    
}
