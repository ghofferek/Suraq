package at.iaik.suraq.test;

import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.main.Ackermann;
import at.iaik.suraq.main.GraphReduction;
import at.iaik.suraq.main.ITEEquationReduction;
import at.iaik.suraq.main.Suraq;
import at.iaik.suraq.util.FormulaCache;

public class EclEmmaTest {

    @Test
    public void performFullSuraq3_no_readonly_pipeline_ex_suraq() { 
        setUp2();
        System.out.println("****************************************************");
        //Ackermann.setPredicateActive(false);
        String[] args = { "-i",
        "./rsc/test/no_readonly_pipeline_example_suraq.smt2"}; //, "-v", "--check-result"
        Suraq suraq = new Suraq(args);
        suraq.run();
        FormulaCache.printStatistic();
        Assert.assertTrue(suraq.success());
    }
    
    public void setUp2() {
        try {
            //SuraqOptions.kill();
            //SuraqOptions.reset();
           // Z3Proof.setInstanceCounter(0);

            Ackermann.setActive(true);
            ITEEquationReduction.setActive(true);
            GraphReduction.setActive(true);
            //QBFSolver.setActive(false);
        } catch (Throwable e) {
            e.printStackTrace();

        }
    }
}
