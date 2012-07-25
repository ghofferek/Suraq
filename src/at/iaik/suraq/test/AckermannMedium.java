package at.iaik.suraq.test;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import at.iaik.suraq.main.Ackermann;
import at.iaik.suraq.main.GraphReduction;
import at.iaik.suraq.main.ITEEquationReduction;
import at.iaik.suraq.main.QBFEncoder;
import at.iaik.suraq.main.QBFSolver;
import at.iaik.suraq.main.Suraq;
import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.util.FormulaCache;

public class AckermannMedium {

    @Before
    public void setUp() {
        SuraqOptions.kill();
        SuraqOptions.reset();
        Z3Proof.setInstanceCounter(0);
        
        Ackermann.setActive(true);
        ITEEquationReduction.setActive(true);
        GraphReduction.setActive(true);
        //QBFSolver.setActive(true);
    }
    
    ///////////////////////////////////////////////////////////////////////////////
    // Here are the tests that call the full Suraq.run() Method
    
    // contains PropITE containing DomainEq with DomainITE
    @Test
    public void performFullSuraq2_simple_3_input_dependent_2_controllers() { 
        System.out.println("****************************************************");
        
        String[] args = { "-i",
        "./rsc/test/input_dependent_2_controllers.smt2"}; //, "-v", "--check-result"
        Suraq suraq = new Suraq(args);
        suraq.run();
        FormulaCache.printStatistic();
        Assert.assertTrue(suraq.success());
    }
    
    
    // contains simple ITE, UF, control signals, nodependence
    @Test
    public void performFullSuraq1_simple_2_controllers() { 
        System.out.println("****************************************************");
        
        String[] args = { "-i",
        "./rsc/test/simple_2_controllers.smt2"}; //, "-v", "--check-result"
        Suraq suraq = new Suraq(args);
        suraq.run();
        FormulaCache.printStatistic();
        Assert.assertTrue(suraq.success());
    }
    
    // Interessanter Fall
    @Test
    public void performFullSuraq3_no_readonly_pipeline_ex_suraq() { 
        System.out.println("****************************************************");
        //Ackermann.setPredicateActive(false);
        String[] args = { "-i",
        "./rsc/test/no_readonly_pipeline_example_suraq.smt2"}; //, "-v", "--check-result"
        Suraq suraq = new Suraq(args);
        suraq.run();
        FormulaCache.printStatistic();
        Assert.assertTrue(suraq.success());
    }

}
