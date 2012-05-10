/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import java.util.ArrayList;
import java.util.List;

import junit.framework.Assert;

import org.junit.Test;

import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalEq;
import at.iaik.suraq.smtlib.formula.PropositionalTerm;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;

/**
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
public class ConsequentTransformationTest {
    /**
     * Tests transformation of single positive literal a --> OR a
     */
    @Test
    public void testSinglePosLiteral() {

        // define input
        Formula input = new PropositionalVariable("a");

        // create expected output
        ArrayList<Formula> subFormulas = new ArrayList<Formula>();
        subFormulas.add(input);
        Formula expectedOutput = new OrFormula(subFormulas);

        // create output with transformation
        Formula output = input.transformToConsequentsForm();

        Assert.assertEquals(expectedOutput.toString(), output.toString());
    }

    /**
     * Tests transformation of single negative literal NOT a --> OR NOT a
     */
    @Test
    public void testSingleNegLiteral() {

        // define input
        Formula input = new NotFormula(new PropositionalVariable("a"));

        // create expected output
        ArrayList<Formula> subFormulas = new ArrayList<Formula>();
        subFormulas.add(input);
        Formula expectedOutput = new OrFormula(subFormulas);

        // create output with transformation
        Formula output = input.transformToConsequentsForm();

        Assert.assertEquals(expectedOutput.toString(), output.toString());
    }

    /**
     * Tests removal multiple negation NOT NOT NOT a --> OR NOT a
     */
    @Test
    public void testRemoveMultipleNots() {

        // define input
        Formula propVar = new PropositionalVariable("a");
        Formula input = new NotFormula(new NotFormula(new NotFormula(propVar)));

        // create expected output
        ArrayList<Formula> subFormulas = new ArrayList<Formula>();
        subFormulas.add(new NotFormula(propVar));
        Formula expectedOutput = new OrFormula(subFormulas);

        // create output with transformation
        Formula output = input.transformToConsequentsForm();

        Assert.assertEquals(expectedOutput.toString(), output.toString());
    }

    /**
     * Tests rewriting implication rule a => b --> NOT a OR b
     */
    @Test
    public void testRewriteImplies() {

        // define input
        PropositionalTerm a = new PropositionalVariable("a");
        PropositionalTerm b = new PropositionalVariable("b");
        Formula input = new ImpliesFormula(a, b);

        // create expected output

        ArrayList<Formula> subFormulas = new ArrayList<Formula>();
        subFormulas.add(new NotFormula(a));
        subFormulas.add(b);
        Formula expectedOutput = new OrFormula(subFormulas);

        // create output with transformation
        Formula output = input.transformToConsequentsForm();
        System.out.println(output.toString() + "\n\n\n"
                + expectedOutput.toString());
        Assert.assertEquals(expectedOutput.toString(), output.toString());
    }

    /**
     * Tests rewriting of inequality a != b --> OR NOT (a = b)
     */
    @Test
    public void testRewriteInequality() {

        // define input
        PropositionalTerm a = new PropositionalVariable("a");
        PropositionalTerm b = new PropositionalVariable("b");
        List<PropositionalTerm> inputFormulas = new ArrayList<PropositionalTerm>();
        inputFormulas.add(a);
        inputFormulas.add(b);
        Formula input = new PropositionalEq(inputFormulas, false);

        // create expected output
        Formula equality = new PropositionalEq(inputFormulas, true);
        ArrayList<Formula> subFormulas = new ArrayList<Formula>();
        subFormulas.add(new NotFormula(equality));
        Formula expectedOutput = new OrFormula(subFormulas);

        // create output with transformation
        Formula output = input.transformToConsequentsForm();

        Assert.assertEquals(expectedOutput.toString(), output.toString());
    }

    /**
     * Tests apply deMorgan rule NOT (a AND b) --> NOT a OR NOT b
     */
    @Test
    public void testApplyDeMorgan() {

        // define input
        PropositionalTerm a = new PropositionalVariable("a");
        PropositionalTerm b = new PropositionalVariable("b");
        List<Formula> inputFormulas = new ArrayList<Formula>();
        inputFormulas.add(a);
        inputFormulas.add(b);
        Formula input = new NotFormula(new AndFormula(inputFormulas));

        // create expected output
        ArrayList<Formula> subFormulas = new ArrayList<Formula>();
        subFormulas.add(new NotFormula(a));
        subFormulas.add(new NotFormula(b));
        Formula expectedOutput = new OrFormula(subFormulas);

        // create output with transformation
        Formula output = input.transformToConsequentsForm();

        Assert.assertEquals(expectedOutput.toString(), output.toString());
    }

    /**
     * Tests nested or operations (a or ( b or c ) ) --> (a or b or c )
     */
    @Test
    public void testNestedOrOperations() {

        // define input
        PropositionalTerm a = new PropositionalVariable("a");
        PropositionalTerm b = new PropositionalVariable("b");
        PropositionalTerm c = new PropositionalVariable("c");

        List<Formula> inputOr1Formulas = new ArrayList<Formula>();
        inputOr1Formulas.add(b);
        inputOr1Formulas.add(c);
        Formula or1Formula = new OrFormula(inputOr1Formulas);

        List<Formula> inputOr2Formulas = new ArrayList<Formula>();
        inputOr2Formulas.add(a);
        inputOr2Formulas.add(or1Formula);
        Formula input = new OrFormula(inputOr2Formulas);

        // create expected output
        List<Formula> subFormulas = new ArrayList<Formula>();
        subFormulas.add(a);
        subFormulas.add(b);
        subFormulas.add(c);
        Formula expectedOutput = new OrFormula(subFormulas);

        // create output with transformation
        Formula output = input.transformToConsequentsForm();

        Assert.assertEquals(expectedOutput.toString(), output.toString());
    }

}