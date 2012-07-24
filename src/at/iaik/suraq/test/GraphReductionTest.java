package at.iaik.suraq.test;

import java.util.ArrayList;
import java.util.HashSet;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import at.iaik.suraq.main.Ackermann;
import at.iaik.suraq.main.GraphReduction;
import at.iaik.suraq.main.ITEEquationReduction;
import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.util.DebugHelper;

/**
 * This class tests if the Ackermann's reduction works.
 * It is not possible to perform all tests, only:
 * * the given formula is unsatisfiable
 * * the given formula is valid
 * @author chillebold
 *
 */
public class GraphReductionTest {
	//SuraqOptions options;
	protected Formula     consequent = null;
    protected TestHelper  th         = new TestHelper();
    
	public GraphReductionTest()
	{
		//options = SuraqOptions.getInstance();
	}
	
	@Before
	public void setUp() {
        Ackermann.setActive(true);
        ITEEquationReduction.setActive(true);
	    GraphReduction.setActive(true);
	    
	    SuraqOptions.kill();
	    SuraqOptions.reset();
	    Z3Proof.setInstanceCounter(0);
	}

	
	// first simple test
	@Test
	public void graphReductionSimple() {  
        System.out.println("****************************************************");
        System.out.println("Testcase: Live: "+"./rsc/test/gr1.smt2");
		boolean result = testFile("./rsc/test/gr1.smt2","./rsc/test/~gr1-reduced.smt2", "./rsc/test/~gr1-valid.smt2");
		System.out.println("  live: " + (result?"Success :-)":"Failed :-("));
	    Assert.assertTrue(result);
	}
	

    // Tests boolean equivalences (must not be substituted)
    @Test
    public void graphReduction2() {  
        System.out.println("****************************************************");
        System.out.println("Testcase: Live: "+"./rsc/test/gr2.smt2");
        boolean result = testFile("./rsc/test/gr2.smt2","./rsc/test/~gr2-reduced.smt2", "./rsc/test/~gr2-valid.smt2");
        System.out.println("  live: " + (result?"Success :-)":"Failed :-("));
        Assert.assertTrue(result);
    }

    // Tests boolean equivalences with inner DomainVars
    @Test
    public void graphReduction3() {  
        System.out.println("****************************************************");
        System.out.println("Testcase: Live: "+"./rsc/test/gr3.smt2");
        boolean result = testFile("./rsc/test/gr3.smt2","./rsc/test/~gr3-reduced.smt2", "./rsc/test/~gr3-valid.smt2");
        System.out.println("  live: " + (result?"Success :-)":"Failed :-("));
        Assert.assertTrue(result);
    }

    // Tests recursive ite
    @Test
    public void graphReduction4() {  
        System.out.println("****************************************************");
        System.out.println("Testcase: Live: "+"./rsc/test/gr4.smt2");
        boolean result = testFile("./rsc/test/gr4.smt2","./rsc/test/~gr4-reduced.smt2", "./rsc/test/~gr4-valid.smt2");
        System.out.println("  live: " + (result?"Success :-)":"Failed :-("));
        Assert.assertTrue(result);
    }
    
    // Live: Ständig zum Herumprobieren
    @Test
    public void graphReductionMedium() {  
        System.out.println("****************************************************");
        System.out.println("Testcase: Live: "+"./rsc/test/a07.smt2");
        boolean result = testFile("./rsc/test/a07.smt2","./rsc/test/~a07-reduced.smt2", "./rsc/test/~a07-valid.smt2");
        System.out.println("  live: " + (result?"Success :-)":"Failed :-("));
        Assert.assertTrue(result);
    }
    
	///////////////////////////////////////////////////////////////////////////////
	
	
	protected boolean testFile(String filename, String outputFileName1, String outputFileName2)
	{
		Formula formula = th.getFormulaOfFile(filename);
		
		Formula old_formula = formula.deepFormulaCopy();
        HashSet<Token> t = new HashSet<Token>();
		
        

        
		// Ackermann
		Ackermann ack = new Ackermann();
		formula = ack.performAckermann(formula, t);
		
		ITEEquationReduction itered = new ITEEquationReduction();
		formula = itered.performReduction(formula, t);
        //formula = formula.removeDomainITE(formula, new HashSet<Token>());
		DebugHelper.getInstance().formulaToFile(formula, "debug_ite.txt");
		
        // Graph Reduction
		GraphReduction gr = new GraphReduction();
		try{
		    formula = gr.perform(formula, t);
		}
		catch(Exception ex)
		{
		    ex.printStackTrace();
		    return false;
		}
				
		// Debug output of Ackermann's result to Filesystem
		String ackermannstr = th.transformFormulaToString(formula);
		th.writeFile(outputFileName1, ackermannstr);
		
		Formula x = formula;
		
		th.isFormulaSat(old_formula, "OLD");
		th.isFormulaSat(formula, "GRAPHRED");

		th.isFormulaValid(old_formula, "OLD");
		th.isFormulaValid(formula, "GRAPHRED");
        
		
		// this only works for VALID formulas
		ImpliesFormula f1 = new ImpliesFormula(old_formula, x);
		ImpliesFormula f2 = new ImpliesFormula(x, old_formula);
		ArrayList<Formula> f12 = new ArrayList<Formula>();
		f12.add(f1);
		f12.add(f2);
		AndFormula equiv = new AndFormula(f12);
		
		// Test Output
		String z3InputStr = th.transformFormulaToString(equiv);
		th.writeFile(outputFileName2, z3InputStr);
        
		// Check if OK:
		boolean valid = th.isFormulaValid(equiv, "Formeln äquivalent");

        if(valid)
        {
            System.out.println("  Z3 tells us UNSAT (valid). Good :-)");
            return true;
        }
        else
        {
            System.err.println("  Z3 tells us SAT. Bad :-(");
            return false;
        }
	}
	

}
