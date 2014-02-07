package at.iaik.suraq.test;

import java.util.ArrayList;
import java.util.HashSet;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import at.iaik.suraq.main.Ackermann;
import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;

/**
 * This class tests if the Ackermann's reduction works. It is not possible to
 * perform all tests, only: * the given formula is unsatisfiable * the given
 * formula is valid
 * 
 * @author chillebold
 * 
 */
public class AckermannPredicatesTest {
    // SuraqOptions options;
    protected Formula consequent;
    protected TestHelper th = new TestHelper();

    public AckermannPredicatesTest() {
        // options = SuraqOptions.getInstance();
    }

    @Before
    public void setUp() {
        SuraqOptions.kill();
        SuraqOptions.reset();
        Z3Proof.setInstanceCounter(0);
    }

    // Live: Staendig zum Herumprobieren
    @Test
    public void liveTest() {
        System.out
                .println("****************************************************");
        System.out.println("Testcase: Live: " + "./rsc/test/ack-prae1.smt2");
        boolean result = testFile("./rsc/test/ack-prae1.smt2",
                "./rsc/test/~ack-prae1-acker.smt2",
                "./rsc/test/~ack-unsat.smt2");
        System.out
                .println("  live: " + (result ? "Success :-)" : "Failed :-("));
        Assert.assertTrue(result);
    }

    // /////////////////////////////////////////////////////////////////////////////

    protected boolean testFile(String filename, String outputFileName1,
            String outputFileName2) {
        Formula formula = th.getFormulaOfFile(filename);

        if (formula == null) {
            System.err.println("formula == null");
            return false;
        }
        Formula old_formula = formula.deepFormulaCopy();

        // Ackermann
        Ackermann ack = new Ackermann();
        HashSet<Token> t = new HashSet<Token>();
        formula = ack.performAckermann(formula, t);

        // Debug output of Ackermann's result to Filesystem
        String ackermannstr = th.transformFormulaToString(formula);
        th.writeFile(outputFileName1, ackermannstr);

        Formula x = formula;

        th.isFormulaSat(old_formula, "OLD");
        th.isFormulaSat(formula, "ACKER");

        th.isFormulaValid(old_formula, "OLD");
        th.isFormulaValid(formula, "ACKER");

        // this only works for VALID formulas
        ImpliesFormula f1 = ImpliesFormula.create(old_formula, x);
        ImpliesFormula f2 = ImpliesFormula.create(x, old_formula);
        ArrayList<Formula> f12 = new ArrayList<Formula>();
        f12.add(f1);
        f12.add(f2);
        AndFormula equiv = AndFormula.generate(f12);

        // Test Output
        String z3InputStr = th.transformFormulaToString(equiv);
        th.writeFile(outputFileName2, z3InputStr);

        // Check if OK:
        boolean valid = th.isFormulaValid(equiv, "Formeln aequivalent");

        if (valid) {
            System.out.println("  Z3 tells us UNSAT (valid). Good :-)");
            return true;
        } else {
            System.err.println("  Z3 tells us SAT. Bad :-(");
            return false;
        }
    }

}
