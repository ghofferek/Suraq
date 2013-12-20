/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.util.CongruenceClosure;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class CongruenClosureTest {

    /**
     * Tests a specific node from dlx_2_controllers proof.
     * 
     * @throws Exception
     * 
     */
    @Test
    public void testClausec40189() throws Exception {

        // (set .c40189 (trans_congr :clauses ()
        // :conclusions (
        //
        // ( not ( = read_fresh1_copy_1 ( PLUS ( short-immed-of ( IMEM
        // PCci4__copy_1 ) ) ZERO ) ))
        // ( not ( = ( PLUS ( short-immed-of ( IMEM PCci4__copy_1 ) ) ZERO )
        // read_fresh13_copy_1 ))
        // ( not ( = read_fresh13_copy_1 read_fresh2_copy_1 ))
        // ( not ( = read_fresh22_copy_1 read_fresh2_copy_1 ))
        // ( not ( = read_fresh22_copy_1 ( rf2-of inst-idsc1__copy_1 ) ))
        // ( not ( = read_fresh11_copy_4 ( rf2-of ( IMEM PCci4__copy_4 ) ) ))
        // ( not ( = ( rf1-of ( IMEM PCci4__copy_4 ) ) read_fresh11_copy_4 ))
        // ( not ( = ( rf1-of inst-idsc1__copy_1 ) read_fresh20_copy_1 ))
        // ( = read_fresh1_copy_1 read_fresh20_copy_1)
        // ( not ( = inst-idsc1__copy_1 ( IMEM PC ) ))
        // ( not ( = PC PCci4__copy_4 )))))

        DomainVariable read_fresh1_copy_1 = DomainVariable
                .create("read_fresh1_copy_1");
        DomainVariable PCci4__copy_1 = DomainVariable.create("PCci4__copy_1");
        DomainVariable PCci4__copy_4 = DomainVariable.create("PCci4__copy_4");
        DomainVariable ZERO = DomainVariable.create("ZERO");
        DomainVariable read_fresh13_copy_1 = DomainVariable
                .create("read_fresh13_copy_1");
        DomainVariable read_fresh2_copy_1 = DomainVariable
                .create("read_fresh2_copy_1");
        DomainVariable read_fresh22_copy_1 = DomainVariable
                .create("read_fresh22_copy_1");
        DomainVariable inst_idsc1__copy_1 = DomainVariable
                .create("inst-idsc1__copy_1");
        DomainVariable read_fresh11_copy_4 = DomainVariable
                .create("read_fresh11_copy_4");
        DomainVariable read_fresh20_copy_1 = DomainVariable
                .create("read_fresh20_copy_1");
        DomainVariable PC = DomainVariable.create("PC");

        UninterpretedFunction PLUS = UninterpretedFunction.create("PLUS", 2,
                SExpressionConstants.VALUE_TYPE);
        UninterpretedFunction IMEM = UninterpretedFunction.create("IMEM", 1,
                SExpressionConstants.VALUE_TYPE);
        UninterpretedFunction short_immed_of = UninterpretedFunction.create(
                "short-immed-of", 1, SExpressionConstants.VALUE_TYPE);
        UninterpretedFunction rf1_of = UninterpretedFunction.create("rf1-of",
                1, SExpressionConstants.VALUE_TYPE);
        UninterpretedFunction rf2_of = UninterpretedFunction.create("rf2-of",
                1, SExpressionConstants.VALUE_TYPE);

        UninterpretedFunctionInstance IMEM_PC = UninterpretedFunctionInstance
                .create(IMEM, PC);
        UninterpretedFunctionInstance IMEM_PCci4__copy_1 = UninterpretedFunctionInstance
                .create(IMEM, PCci4__copy_1);
        UninterpretedFunctionInstance IMEM_PCci4__copy_4 = UninterpretedFunctionInstance
                .create(IMEM, PCci4__copy_4);
        UninterpretedFunctionInstance short_immed_of_IMEM_PCci4__copy_1 = UninterpretedFunctionInstance
                .create(short_immed_of, IMEM_PCci4__copy_1);
        UninterpretedFunctionInstance rf2_of_inst_idsc1__copy_1 = UninterpretedFunctionInstance
                .create(rf2_of, inst_idsc1__copy_1);
        UninterpretedFunctionInstance rf2_of_IMEM_PCci4__copy_4 = UninterpretedFunctionInstance
                .create(rf2_of, IMEM_PCci4__copy_4);
        UninterpretedFunctionInstance rf1_of_IMEM_PCci4__copy_4 = UninterpretedFunctionInstance
                .create(rf1_of, IMEM_PCci4__copy_4);
        UninterpretedFunctionInstance rf1_of_inst_idsc1__copy_1 = UninterpretedFunctionInstance
                .create(rf1_of, inst_idsc1__copy_1);

        List<DomainTerm> parameters = new ArrayList<DomainTerm>(2);
        parameters.add(short_immed_of_IMEM_PCci4__copy_1);
        parameters.add(ZERO);
        UninterpretedFunctionInstance PLUS_short_immed_of_IMEM_PCci4__copy_1_ZERO = UninterpretedFunctionInstance
                .create(PLUS, parameters);

        DomainEq[] literals = new DomainEq[10];
        literals[0] = createEquality(read_fresh1_copy_1,
                PLUS_short_immed_of_IMEM_PCci4__copy_1_ZERO);
        literals[1] = createEquality(
                PLUS_short_immed_of_IMEM_PCci4__copy_1_ZERO,
                read_fresh13_copy_1);
        literals[2] = createEquality(read_fresh13_copy_1, read_fresh2_copy_1);
        literals[3] = createEquality(read_fresh22_copy_1, read_fresh2_copy_1);
        literals[4] = createEquality(read_fresh22_copy_1,
                rf2_of_inst_idsc1__copy_1);
        literals[5] = createEquality(read_fresh11_copy_4,
                rf2_of_IMEM_PCci4__copy_4);
        literals[6] = createEquality(rf1_of_IMEM_PCci4__copy_4,
                read_fresh11_copy_4);
        literals[7] = createEquality(rf1_of_inst_idsc1__copy_1,
                read_fresh20_copy_1);
        literals[8] = createEquality(inst_idsc1__copy_1, IMEM_PC);
        literals[9] = createEquality(PC, PCci4__copy_4);

        DomainEq impliedLiteral = createEquality(read_fresh1_copy_1,
                read_fresh20_copy_1);

        CongruenceClosure cc = new CongruenceClosure();
        for (DomainEq literal : literals) {
            cc.addEquality(literal);
        }

        Assert.assertTrue(cc.checkImplied(impliedLiteral));

        Assert.assertEquals(7, cc.getNumEquivClasses());

    }

    private DomainEq createEquality(DomainTerm term1, DomainTerm term2) {
        List<DomainTerm> list = new ArrayList<DomainTerm>(2);
        list.add(term1);
        list.add(term2);
        return DomainEq.create(list, true);
    }
}
