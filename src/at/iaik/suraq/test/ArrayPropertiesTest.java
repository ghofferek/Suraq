/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import junit.framework.Assert;

import org.junit.Test;

import at.iaik.suraq.exceptions.InvalidIndexGuardException;
import at.iaik.suraq.exceptions.InvalidValueConstraintException;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.ArrayProperty;
import at.iaik.suraq.smtlib.formula.ArrayRead;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayPropertiesTest {

    /**
     * Test method for
     * {@link at.iaik.suraq.smtlib.formula.ArrayProperty#arrayPropertiesToFiniteConjunctions(java.util.Set)}
     * .
     * 
     * @throws InvalidValueConstraintException
     * @throws InvalidIndexGuardException
     */
    @Test
    public void testArrayPropertiesToFiniteConjunctions()
            throws InvalidIndexGuardException, InvalidValueConstraintException {
        DomainVariable uVar = new DomainVariable("uVar");
        DomainVariable i1 = new DomainVariable("i1");
        DomainVariable i2 = new DomainVariable("i2");
        DomainVariable i3 = new DomainVariable("i3");
        DomainVariable constant = new DomainVariable("constant");

        ArrayVariable array = new ArrayVariable("array");
        ArrayRead read = new ArrayRead(array, uVar);

        List<DomainTerm> list = new ArrayList<DomainTerm>();
        list.add(read);
        list.add(constant);

        List<DomainVariable> uVars = new ArrayList<DomainVariable>();
        uVars.add(uVar);

        Formula indexGuard = new PropositionalConstant(true);
        Formula valueConstraint = new DomainEq(list, true);

        ArrayProperty property = new ArrayProperty(uVars, indexGuard,
                valueConstraint);

        Set<DomainTerm> indexSet = new HashSet<DomainTerm>();
        indexSet.add(i1);
        indexSet.add(i2);
        indexSet.add(i3);

        AndFormula actual = property.toFiniteConjunction(indexSet);

        List<Formula> conjuncts = new ArrayList<Formula>();
        for (DomainTerm var : indexSet) {
            Formula leftSide = new PropositionalConstant(true);

            read = new ArrayRead(array, var);
            list.clear();
            list.add(read);
            list.add(constant);

            Formula rightSide = new DomainEq(list, true);
            Formula conjunct = new ImpliesFormula(leftSide, rightSide);
            conjuncts.add(conjunct);
        }
        AndFormula expected = AndFormula.generate(conjuncts);

        Assert.assertEquals(expected, actual);
    }

}
