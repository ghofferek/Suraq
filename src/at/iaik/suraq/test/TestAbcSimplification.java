/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.util.FormulaSimplifier;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TestAbcSimplification {

    @Test
    public void test() throws Exception {

        List<Term> terms = new ArrayList<Term>();
        List<Formula> formulas = new ArrayList<Formula>();

        DomainVariable a = DomainVariable.create("a");
        DomainVariable b = DomainVariable.create("b");
        DomainVariable c = DomainVariable.create("c");
        DomainVariable d = DomainVariable.create("d");
        DomainVariable e = DomainVariable.create("e");

        terms.clear();
        terms.add(a);
        terms.add(b);
        DomainEq aEqb = (DomainEq) EqualityFormula.create(terms, true);
        terms.clear();
        terms.add(b);
        terms.add(c);
        DomainEq bEqc = (DomainEq) EqualityFormula.create(terms, true);
        terms.clear();
        terms.add(c);
        terms.add(d);
        DomainEq cEqd = (DomainEq) EqualityFormula.create(terms, true);
        terms.clear();
        terms.add(d);
        terms.add(e);
        DomainEq dEqe = (DomainEq) EqualityFormula.create(terms, true);

        formulas.clear();
        formulas.add(aEqb);
        formulas.add(PropositionalConstant.create(false));
        AndFormula and1 = AndFormula.generate(formulas);
        formulas.clear();
        formulas.add(cEqd);
        formulas.add(PropositionalConstant.create(true));
        AndFormula and2 = AndFormula.generate(formulas);
        formulas.clear();
        formulas.add(NotFormula.create(bEqc));
        formulas.add(dEqe);
        AndFormula and3 = AndFormula.generate(formulas);
        formulas.clear();
        formulas.add(cEqd);
        formulas.add(cEqd);
        AndFormula and4 = AndFormula.generate(formulas);

        formulas.clear();
        formulas.add(and1);
        formulas.add(and2);
        OrFormula or1 = OrFormula.generate(formulas);
        formulas.clear();
        formulas.add(NotFormula.create(and3));
        formulas.add(and4);
        OrFormula or2 = OrFormula.generate(formulas);

        ImpliesFormula impl = ImpliesFormula.create(or1, or2);

        formulas.clear();
        formulas.add(impl);
        formulas.add(PropositionalConstant.create(false));
        OrFormula or3 = OrFormula.generate(formulas);

        FormulaSimplifier simplifier = new FormulaSimplifier(or3);
        simplifier.simplify();
        boolean result = simplifier.checkSimplification();
        System.out.println("Check result: " + result);
    }

    public void run() throws Exception {
        test();
    }

    public static void main(String[] args) {
        try {
            TestAbcSimplification instance = new TestAbcSimplification();
            instance.run();
        } catch (Throwable exc) {
            exc.printStackTrace();
        }
    }

}
