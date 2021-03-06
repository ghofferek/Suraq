/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.ArrayEq;
import at.iaik.suraq.smtlib.formula.ArrayProperty;
import at.iaik.suraq.smtlib.formula.ArrayRead;
import at.iaik.suraq.smtlib.formula.ArrayTerm;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.ArrayWrite;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ApplyWriteAxiomTest {

    @Test
    public void testApplyWriteAxiom() throws Throwable {
        ArrayVariable arrayVar = ArrayVariable.create("A");
        DomainVariable index = DomainVariable.create("i");
        DomainVariable value = DomainVariable.create("v");

        ArrayWrite write = ArrayWrite.create(arrayVar, index, value);
        Set<Formula> constraints = new HashSet<Formula>();
        Set<Token> noDependenceVars = new HashSet<Token>();
        List<ArrayTerm> list = new ArrayList<ArrayTerm>();
        list.add(arrayVar);
        list.add(arrayVar);
        Formula topLevelFormula = ArrayEq.create(list, true);

        ArrayVariable newVar = write.applyWriteAxiom(topLevelFormula,
                constraints, noDependenceVars);

        Assert.assertNotSame(arrayVar, newVar);

        Assert.assertEquals(2, constraints.size());
        for (Formula constraint : constraints) {
            Assert.assertTrue(constraint instanceof DomainEq
                    || constraint instanceof ArrayProperty);

            if (constraint instanceof DomainEq) {
                DomainEq eq = (DomainEq) constraint;
                Assert.assertTrue(eq.getDomainTerms().size() == 2);
                DomainTerm term1 = eq.getDomainTerms().get(0);
                DomainTerm term2 = eq.getDomainTerms().get(1);
                ArrayRead read;
                DomainVariable v;
                Assert.assertTrue(term1 instanceof ArrayRead
                        || term2 instanceof ArrayRead);
                Assert.assertTrue(term1 instanceof DomainVariable
                        || term2 instanceof DomainVariable);
                if (term1 instanceof ArrayRead) {
                    read = (ArrayRead) term1;
                    v = (DomainVariable) term2;
                } else {
                    read = (ArrayRead) term2;
                    v = (DomainVariable) term1;
                }

                Assert.assertEquals(value, v);
                ArrayRead expectedRead = ArrayRead.create(newVar, index);
                Assert.assertEquals(expectedRead, read);

            } else { // Array Property
                ArrayProperty property = (ArrayProperty) constraint;
                Assert.assertEquals(1, property.getuVars().size());
                Assert.assertTrue(property.getIndexGuard() instanceof DomainEq);
                Assert.assertFalse(((DomainEq) (property.getIndexGuard()))
                        .isEqual());
                Assert.assertEquals(2,
                        ((DomainEq) (property.getIndexGuard())).numTerms());
                Assert.assertTrue(((DomainEq) (property.getIndexGuard()))
                        .getTerms().get(0) instanceof DomainVariable);
                Assert.assertTrue(((DomainEq) (property.getIndexGuard()))
                        .getTerms().get(1) instanceof DomainVariable);

                Assert.assertTrue(property.getValueConstraint() instanceof DomainEq);
                Assert.assertTrue(((DomainEq) (property.getValueConstraint()))
                        .isEqual());
                Assert.assertEquals(2,
                        ((DomainEq) (property.getIndexGuard())).numTerms());
                Assert.assertTrue(((DomainEq) (property.getValueConstraint()))
                        .getTerms().get(0) instanceof ArrayRead);
                Assert.assertTrue(((DomainEq) (property.getValueConstraint()))
                        .getTerms().get(1) instanceof ArrayRead);
            }

        }
    }
}
