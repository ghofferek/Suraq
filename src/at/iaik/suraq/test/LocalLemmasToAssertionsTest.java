/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import java.util.HashSet;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.parser.ProofParser;
import at.iaik.suraq.parser.SExpParser;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;

/**
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
public class LocalLemmasToAssertionsTest {

    /**
     * Tests the transformation of local lemmas to assertions.
     */
    @Test
    public void test1LocalLemmaToAssertion() {

        Set<DomainVariable> domainVars = new HashSet<DomainVariable>();
        Set<PropositionalVariable> propsitionalVars = new HashSet<PropositionalVariable>();
        Set<UninterpretedFunction> uninterpretedFunctions = new HashSet<UninterpretedFunction>();
        Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();

        domainVars.add(DomainVariable.create("a"));
        domainVars.add(DomainVariable.create("b"));
        domainVars.add(DomainVariable.create("c"));

        String transitivity = "(trans (asserted (= a b)) (asserted (= b c)) (= a c))";
        String resolution = "(|unit-resolution| " + transitivity
                + " (asserted (not (= a c))) false )";
        String proof = "(lemma " + resolution + "(not (= a b)))";

        String output = parseAndRemoveLocalLemmas(proof, domainVars,
                propsitionalVars, uninterpretedFunctions, arrayVars);

        String expectedOutput = "( asserted ( not ( = a b ) ))";

        Assert.assertEquals(expectedOutput, output);

    }

    /**
     * Tests the transformation of local lemmas to assertions.
     */
    @Test
    public void test2LocalLemmaToAssertion() {

        Set<DomainVariable> domainVars = new HashSet<DomainVariable>();
        Set<PropositionalVariable> propsitionalVars = new HashSet<PropositionalVariable>();
        Set<UninterpretedFunction> uninterpretedFunctions = new HashSet<UninterpretedFunction>();
        Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();

        domainVars.add(DomainVariable.create("a", 1));
        domainVars.add(DomainVariable.create("b"));
        domainVars.add(DomainVariable.create("c", 2));

        String transitivity = "(trans (asserted (= a b)) (asserted (= b c)) (= a c))";
        String resolution = "(|unit-resolution| " + transitivity
                + " (asserted (not (= a c))) false )";
        String proof = "(lemma " + resolution + "(not (= a b)))";

        String output = parseAndRemoveLocalLemmas(proof, domainVars,
                propsitionalVars, uninterpretedFunctions, arrayVars);

        String expectedOutput = "( lemma ( |unit-resolution| ( trans ( asserted ( = a b ) ) "
                + "( asserted ( = b c ) ) ( = a c ) ) "
                + "( asserted ( not ( = a c ) ) ) false ) ( not ( = a b ) ))";

        Assert.assertEquals(expectedOutput, output);

    }

    /**
     * Helper function to parse the proof and transform local lemmas in the
     * proof to assertions.
     * 
     * @param proof
     *            proof string to be parsed
     * @param domainVars
     *            set of <code>DomainVariable</code> contained in the proof
     * @param propsitionalVars
     *            set of <code>PropsitionalVariable</code> contained in the
     *            proof
     * @param uninterpretedFunctions
     *            set of <code>UninterpretedFunction</code> contained in the
     *            proof
     * @param arrayVars
     *            set of <code>ArrayVariable</code> contained in the proof
     * @return parsed and transformed proof
     */

    @SuppressWarnings("deprecation")
    private String parseAndRemoveLocalLemmas(String proof,
            Set<DomainVariable> domainVars,
            Set<PropositionalVariable> propsitionalVars,
            Set<UninterpretedFunction> uninterpretedFunctions,
            Set<ArrayVariable> arrayVars) {

        // expression parsing of proof
        SExpParser sExpProofParser = null;
        sExpProofParser = new SExpParser(proof);

        try {
            sExpProofParser.parse();
            assert (sExpProofParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            throw new RuntimeException("SExpression Parse Error in Testcase: "
                    + exc);
        }

        // parsing proof
        ProofParser proofParser = new ProofParser(
                sExpProofParser.getRootExpr(), domainVars, propsitionalVars,
                arrayVars, uninterpretedFunctions);

        try {
            proofParser.parse();
            assert (proofParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            throw new RuntimeException("Proof Parse Error in Testcase: " + exc);
        }

        Z3Proof rootProof = proofParser.getRootProof();
        rootProof.localLemmasToAssertions();

        return rootProof.toString().replaceAll("\n", "")
                .replaceAll("\\s{2,}", " ");
    }
}