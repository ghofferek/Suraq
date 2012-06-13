/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

/**
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import junit.framework.Assert;

import org.junit.Test;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.parser.SExpParser;
import at.iaik.suraq.parser.TseitinParser;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;

public class TseitinTest {

    /**
     * Tests the transformation of unit-resolution into multiple (simple)
     * resolutions.
     */

    @Test
    public void testUnitResolutionTransformationSimple() {

        String formula = "(goals "
                + "(goal "
                + "(or d k!0)"
                + "(or a k!0)"
                + "(or (not d) (not a) (not k!0))"
                + "(or a k!1)"
                + "(or (not c) k!1)"
                + "(or (not a) c (not k!1))"
                + "(or k!1 k!2)"
                + " (or b k!2)"
                + "(or (not e) k!2)"
                + "(or a k!2)"
                + "(or c k!2)"
                + "(or k!0 k!2)"
                + "(or (not k!1) (not b) e (not a) (not c) (not k!0) (not k!2))"
                + " (or (not k!2) a b)" + ":precision precise :depth 3)" + ")";

        PropositionalVariable a = new PropositionalVariable("a", -1);
        PropositionalVariable b = new PropositionalVariable("b", -1);
        PropositionalVariable c = new PropositionalVariable("c", -1);
        PropositionalVariable d = new PropositionalVariable("d", 2);
        PropositionalVariable e = new PropositionalVariable("e", -1);

        Set<PropositionalVariable> propsitionalVars = new HashSet<PropositionalVariable>();
        propsitionalVars.add(a);
        propsitionalVars.add(b);
        propsitionalVars.add(c);
        propsitionalVars.add(d);
        propsitionalVars.add(e);

        SExpParser sExpParser = new SExpParser(formula);
        try {
            sExpParser.parse();
            assert (sExpParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            exc.printStackTrace();
        }

        SExpression rootExp = sExpParser.getRootExpr();

        TseitinParser tseitinParser = new TseitinParser(rootExp,
                new HashSet<DomainVariable>(), propsitionalVars,
                new HashSet<ArrayVariable>(),
                new HashSet<UninterpretedFunction>());
        try {
            tseitinParser.parse();
            assert (tseitinParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            exc.printStackTrace();
        }

        tseitinParser.getRootFormula();
        Map<PropositionalVariable, Formula> tseitinEncoding = tseitinParser
                .getTseitinEncoding();

        // create expected Output
        Map<PropositionalVariable, Formula> expectedOutput = new HashMap<PropositionalVariable, Formula>();
        ArrayList<Formula> conjuncts = new ArrayList<Formula>();
        conjuncts.add(d);
        conjuncts.add(a);
        Formula notk0 = new AndFormula(conjuncts);
        expectedOutput.put(new PropositionalVariable("k!0", 2), notk0);

        conjuncts = new ArrayList<Formula>();
        conjuncts.add(a);
        conjuncts.add(new NotFormula(c));
        Formula notk1 = new AndFormula(conjuncts);
        expectedOutput.put(new PropositionalVariable("k!1", -1), notk1);

        conjuncts = new ArrayList<Formula>();
        conjuncts.add(new NotFormula(notk1.deepFormulaCopy()));
        conjuncts.add(b);
        conjuncts.add(new NotFormula(e));
        conjuncts.add(a);
        conjuncts.add(c);
        conjuncts.add(new NotFormula(notk0.deepFormulaCopy()));
        Formula notk2 = new AndFormula(conjuncts);
        expectedOutput.put(new PropositionalVariable("k!2", 2), notk2);

        for (Map.Entry<PropositionalVariable, Formula> entry : expectedOutput
                .entrySet()) {
            PropositionalVariable tseitinVar = entry.getKey();
            Formula expectedFormula = entry.getValue();
            Formula actualFormula = tseitinEncoding.get(tseitinVar);
            Assert.assertEquals(expectedFormula.toString(),
                    actualFormula.toString());
        }

    }

}
