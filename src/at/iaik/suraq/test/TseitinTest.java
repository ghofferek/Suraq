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

import org.junit.Assert;
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

        PropositionalVariable a = PropositionalVariable.create("a", -1);
        PropositionalVariable b = PropositionalVariable.create("b", -1);
        PropositionalVariable c = PropositionalVariable.create("c", -1);
        PropositionalVariable d = PropositionalVariable.create("d", 2);
        PropositionalVariable e = PropositionalVariable.create("e", -1);

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
                new HashSet<UninterpretedFunction>(), 0);
        try {
            tseitinParser.parse();
            assert (tseitinParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            exc.printStackTrace();
        }

        tseitinParser.getRootFormula();
        Map<PropositionalVariable, Formula> tseitinEncoding = tseitinParser
                .getTseitinEncoding();

        for (PropositionalVariable var : tseitinEncoding.keySet()) {
            Formula tseitinFormula = tseitinEncoding.get(var);
            System.out.println("****** TSEITIN OF " + var.getVarName()
                    + " ********");
            System.out.println(tseitinFormula.toString());
        }

        // create expected Output
        Map<PropositionalVariable, Formula> expectedOutput = new HashMap<PropositionalVariable, Formula>();
        ArrayList<Formula> conjuncts = new ArrayList<Formula>();
        conjuncts.add(d);
        conjuncts.add(a);
        Formula notk0 = AndFormula.generate(conjuncts);
        expectedOutput.put(PropositionalVariable.create("k!0", 2), notk0);

        conjuncts = new ArrayList<Formula>();
        conjuncts.add(a);
        conjuncts.add(NotFormula.create(c));
        Formula notk1 = AndFormula.generate(conjuncts);
        expectedOutput.put(PropositionalVariable.create("k!1", -1), notk1);

        conjuncts = new ArrayList<Formula>();
        conjuncts.add(NotFormula.create(notk1.deepFormulaCopy()));
        conjuncts.add(b);
        conjuncts.add(NotFormula.create(e));
        conjuncts.add(a);
        conjuncts.add(c);
        conjuncts.add(NotFormula.create(notk0.deepFormulaCopy()));
        Formula notk2 = AndFormula.generate(conjuncts);
        expectedOutput.put(PropositionalVariable.create("k!2", 2), notk2);

        int i = 0;
        for (Map.Entry<PropositionalVariable, Formula> entry : expectedOutput
                .entrySet()) {
            PropositionalVariable tseitinVar = entry.getKey();
            Formula expectedFormula = entry.getValue();
            Formula actualFormula = tseitinEncoding.get(tseitinVar);

            i++;
            System.out.println("[" + i + "] Test: " + tseitinVar.getVarName());
            System.out.println("========== EXPECTED ===============");
            System.out.println("" + expectedFormula.toString());
            System.out.println("========== ACTUAL =================");
            System.out.println("" + actualFormula.toString());
            System.out.println("===================================");

            Assert.assertEquals(expectedFormula.toString(),
                    actualFormula.toString());
        }

    }

}
