package at.iaik.suraq.test;

import java.util.ArrayList;
import java.util.HashSet;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import at.iaik.suraq.main.Ackermann;
import at.iaik.suraq.main.GraphReduction;
import at.iaik.suraq.main.ITEEquationReduction;
import at.iaik.suraq.main.QBFEncoder;
import at.iaik.suraq.main.QBFSolver;
import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.main.TseitinEncoding;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.util.DebugHelper;

public class QBFTest {
    protected TestHelper th = new TestHelper();

    @Before
    public void setUp() throws Exception {

        GraphReduction.setActive(true);
        Ackermann.setActive(true);
        ITEEquationReduction.setActive(true);

        SuraqOptions.kill();
        SuraqOptions.reset();
        Z3Proof.setInstanceCounter(0);
    }

    @Test
    public void test() {
        System.out
                .println("****************************************************");
        System.out.println("Testcase: Live: " + "./rsc/test/gr1.smt2");
        boolean result = testFile("./rsc/test/gr1.smt2",
                "./rsc/test/~gr1-reduced.smt2", "./rsc/test/~gr1-valid.smt2");
        System.out
                .println("  live: " + (result ? "Success :-)" : "Failed :-("));
        Assert.assertTrue(result);
    }

    protected boolean testFile(String filename, String outputFileName1,
            String outputFileName2) {
        GraphReduction.setActive(true);
        Formula formula = th.getFormulaOfFile(filename);

        if (formula == null) {
            System.err.println("formula == null");
            return false;
        }
        Formula old_formula = formula.deepFormulaCopy();
        HashSet<Token> t = new HashSet<Token>();
        // Ackermann
        Ackermann ack = new Ackermann();
        formula = ack.performAckermann(formula, t);

        ITEEquationReduction itered = new ITEEquationReduction();
        formula = itered.perform(formula, t);
        // formula = formula.removeDomainITE(formula, new HashSet<Token>());
        DebugHelper.getInstance().formulaToFile(formula, "debug_ite.txt");

        // Graph Reduction
        GraphReduction gr = new GraphReduction();
        try {
            formula = gr.perform(formula, t);
        } catch (Exception ex) {
            ex.printStackTrace();
            return false;
        }

        // Debug output of Ackermann's result to Filesystem
        String ackermannstr = th.transformFormulaToString(formula);
        th.writeFile(outputFileName1, ackermannstr);

        Formula x = formula;

        th.isFormulaSat(old_formula, "OLD");
        boolean sat = th.isFormulaSat(formula, "GRAPHRED");

        th.isFormulaValid(old_formula, "OLD");
        th.isFormulaValid(formula, "GRAPHRED");

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

        boolean valid = th.isFormulaValid(equiv, "Formeln äquivalent");

        if (valid) {
            System.out.println("  Z3 tells us UNSAT (valid). Good :-)");
            // return true;
        } else {
            System.err.println("  Z3 tells us SAT. Bad :-(");
            // return false;
        }

        ArrayList<PropositionalVariable> tmp = new ArrayList<PropositionalVariable>(
                formula.getPropositionalVariables());

        TseitinEncoding tseitin = new TseitinEncoding();
        formula = tseitin.performTseitinEncodingWithoutZ3(formula);
        DebugHelper.getInstance().formulaToFile(formula, "debug_tseitin.txt");

        QBFEncoder qbfEncoder = new QBFEncoder();
        String smtstr = qbfEncoder.encode(formula, new HashSet<Token>(), tmp,
                tseitin.getPropositionalVariables());

        QBFSolver qbfSolver = new QBFSolver();
        qbfSolver.solve(smtstr);
        if (qbfSolver.getState() == QBFSolver.SAT) {
            return sat;
        } else if (qbfSolver.getState() == QBFSolver.UNSAT) {
            return (!sat);
        } else
            return (false);

    }

}
