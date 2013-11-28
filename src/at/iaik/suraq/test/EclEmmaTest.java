package at.iaik.suraq.test;

import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.main.Ackermann;
import at.iaik.suraq.main.GraphReduction;
import at.iaik.suraq.main.ITEEquationReduction;
import at.iaik.suraq.main.QBFEncoder;
import at.iaik.suraq.main.QBFSolver;
import at.iaik.suraq.main.Suraq;
import at.iaik.suraq.smtsolver.VeriTSolver;
import at.iaik.suraq.util.FormulaCache;

public class EclEmmaTest {

    @Test
    public void no_readonly_pipeline_example_suraq() { 
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

            Ackermann.setActive(false);
            ITEEquationReduction.setActive(false);
            GraphReduction.setActive(false);
            
            VeriTSolver.setActive(true);
            
            QBFEncoder.setActive(false);
            QBFSolver.setActive(false);
            //QBFSolver.setActive(false);
        } catch (Throwable e) {
            e.printStackTrace();

        }
    }
}
