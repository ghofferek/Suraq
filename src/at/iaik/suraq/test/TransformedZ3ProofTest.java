/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import java.util.HashSet;
import java.util.Set;

import junit.framework.Assert;

import org.junit.Test;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.parser.ProofParser;
import at.iaik.suraq.parser.SExpParser;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.smtlib.TransformedZ3Proof;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;

/**
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
public class TransformedZ3ProofTest {

    /**
     * Tests the transformation of unit-resolution into multiple (simple)
     * resolutions.
     */

    @Test
    public void testUnitResolutionTransformationSimple() {

        Set<DomainVariable> domainVars = new HashSet<DomainVariable>();
        Set<PropositionalVariable> propsitionalVars = new HashSet<PropositionalVariable>();
        Set<UninterpretedFunction> uninterpretedFunctions = new HashSet<UninterpretedFunction>();
        Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();

        propsitionalVars.add(new PropositionalVariable("a"));
        propsitionalVars.add(new PropositionalVariable("b"));

        String proof = "(|unit-resolution| (asserted (or a b)) (asserted (not a)) b)";
        String output = parseAndTransform(proof, domainVars, propsitionalVars,
                uninterpretedFunctions, arrayVars);

        String expectedOutput = "( asserted ( or b ))";

        Assert.assertEquals(SExpression.fromString(expectedOutput),
                SExpression.fromString(output));
    }

    /**
     * Tests the transformation of unit-resolution into multiple (simple)
     * resolutions.
     */

    @Test
    public void testUnitResolutionTransformation() {

        Set<DomainVariable> domainVars = new HashSet<DomainVariable>();
        Set<PropositionalVariable> propsitionalVars = new HashSet<PropositionalVariable>();
        Set<UninterpretedFunction> uninterpretedFunctions = new HashSet<UninterpretedFunction>();
        Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();

        propsitionalVars.add(new PropositionalVariable("a", -1));
        propsitionalVars.add(new PropositionalVariable("b", 1));
        propsitionalVars.add(new PropositionalVariable("c", 1));

        String proof = "(|unit-resolution| (asserted (or a b c)) (asserted (not a)) (asserted (not b)) c)";
        String output = parseAndTransform(proof, domainVars, propsitionalVars,
                uninterpretedFunctions, arrayVars);

        String expectedOutput = "( asserted ( or c ))";

        Assert.assertEquals(SExpression.fromString(expectedOutput).toString(),
                SExpression.fromString(output).toString());
    }

    /**
     * Tests the transformation of lemma into resolutions.
     */
    @Test
    public void testLemmaTransformation() {

        Set<DomainVariable> domainVars = new HashSet<DomainVariable>();
        Set<PropositionalVariable> propsitionalVars = new HashSet<PropositionalVariable>();
        Set<UninterpretedFunction> uninterpretedFunctions = new HashSet<UninterpretedFunction>();
        Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();

        propsitionalVars.add(new PropositionalVariable("a", 1));
        propsitionalVars.add(new PropositionalVariable("b", 2));
        propsitionalVars.add(new PropositionalVariable("c"));

        String resolution1 = "(|unit-resolution| (asserted (or (not a) c)) (hypothesis a) c )";
        String resolution2 = "(|unit-resolution| (asserted (or b (not c))) (hypothesis (not b)) (not c) )";
        String resolution3 = "(|unit-resolution| " + resolution1 + resolution2
                + " false)";

        String proof = "(lemma  " + resolution3 + "(or (not a) b))";

        String output = parseAndTransform(proof, domainVars, propsitionalVars,
                uninterpretedFunctions, arrayVars);

        String expectedOutput = "( |unit-resolution|{c} ( asserted ( or c ( not a ) ) ) ( asserted ( or ( not c ) b ) ) ( or ( not a ) b ))";

        Assert.assertEquals(expectedOutput, output);
    }

    /**
     * Tests the transformation of unit-resolution into multiple (simple)
     * resolutions.
     */

    @Test
    public void testTransitivity() {

        Set<DomainVariable> domainVars = new HashSet<DomainVariable>();
        Set<PropositionalVariable> propsitionalVars = new HashSet<PropositionalVariable>();
        Set<UninterpretedFunction> uninterpretedFunctions = new HashSet<UninterpretedFunction>();
        Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();

        propsitionalVars.add(new PropositionalVariable("a", 1));
        propsitionalVars.add(new PropositionalVariable("b", 2));
        propsitionalVars.add(new PropositionalVariable("x", -1));
        propsitionalVars.add(new PropositionalVariable("y", -1));

        String symmetry = "(symm (asserted (= a y)) (= y a))";
        String trans1 = "(trans (asserted (= a x)) (asserted (= x b)) (= a b))";
        String trans2 = "(trans " + symmetry + trans1 + "(= y b))";

        String proof = "(|unit-resolution| " + trans2
                + "(asserted (not (= y b))) false)";

        String output = parseAndTransform(proof, domainVars, propsitionalVars,
                uninterpretedFunctions, arrayVars);

        String expectedOutput = "( asserted ( or c ))";

        Assert.assertEquals(SExpression.fromString(expectedOutput).toString(),
                SExpression.fromString(output).toString());
    }

    /**
     * Helper function to parse and transform a given proof.
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
     */

    private String parseAndTransform(String proof,
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
        rootProof.removeLocalSubProofs();
        rootProof.dealWithModusPonens();
        TransformedZ3Proof transformedZ3Proof = new TransformedZ3Proof(
                rootProof);
        transformedZ3Proof.toLocalProof();
        transformedZ3Proof.toResolutionProof();

        return transformedZ3Proof.toString().replaceAll("\n", "")
                .replaceAll("\\s{2,}", " ");
    }
}