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
import at.iaik.suraq.resProof.ResProof;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.smtlib.TransformedZ3Proof;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.util.Util;

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

        String expectedOutput = "( |unit-resolution|{( = y b)} ( |unit-resolution|{( = x b)} ( asserted ( or ( = x b ) ) ) ( |unit-resolution|{( = y x)} ( |unit-resolution|{( = a x)} ( asserted ( or ( = a x ) ) ) ( |unit-resolution|{( = y a)} ( asserted ( or ( = y a ) ) ) ( asserted ( or ( not ( = y a ) ) ( not ( = a x ) ) ( = y x ) ) ) ( or ( not ( = a x ) ) ( = y x ) ) ) ( or ( = y x ) ) ) ( asserted ( or ( not ( = y x ) ) ( not ( = x b ) ) ( = y b ) ) ) ( or ( not ( = x b ) ) ( = y b ) ) ) ( or ( = y b ) ) ) ( asserted ( or ( not ( = y b ) ) ) ) ( or false ))";

        Assert.assertEquals(SExpression.fromString(expectedOutput).toString(),
                SExpression.fromString(output).toString());
    }

    @Test
    public void testLemma() {

        Set<DomainVariable> domainVars = new HashSet<DomainVariable>();
        Set<PropositionalVariable> propsitionalVars = new HashSet<PropositionalVariable>();
        Set<UninterpretedFunction> uninterpretedFunctions = new HashSet<UninterpretedFunction>();
        Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();

        propsitionalVars.add(new PropositionalVariable("a", 1));
        propsitionalVars.add(new PropositionalVariable("b", 2));
        propsitionalVars.add(new PropositionalVariable("c", 3));
        propsitionalVars.add(new PropositionalVariable("d", 3));
        propsitionalVars.add(new PropositionalVariable("e", -1));
        propsitionalVars.add(new PropositionalVariable("f", -1));

        propsitionalVars.add(new PropositionalVariable("x", -1));
        propsitionalVars.add(new PropositionalVariable("y", -1));

        String unitResolution1 = "(|unit-resolution| (hypothesis (not (= x b))) (asserted (or (= b x) (not (= e f)))) (not (= e f)))";
        String unitResolution2 = "(|unit-resolution| (asserted (or (= c d) (= e f)))"
                + unitResolution1 + "(= c d))";
        String unitResolution3 = "(|unit-resolution| " + unitResolution2
                + " (asserted (not (= c d))) false)";
        String proof = "(lemma " + unitResolution3 + "(= x b))";

        String output = parseAndTransform(proof, domainVars, propsitionalVars,
                uninterpretedFunctions, arrayVars);

        String expectedOutput = "( |unit-resolution|{( = c d)} ( |unit-resolution|{( = e f)} ( asserted ( or ( = c d ) ( = e f ) ) ) ( asserted ( or ( not ( = e f ) ) ( = x b ) ) ) ( or ( = c d ) ( = x b ) ) ) ( asserted ( or ( not ( = c d ) ) ) ) ( or ( = x b ) ))";

        Assert.assertEquals(SExpression.fromString(expectedOutput).toString(),
                SExpression.fromString(output).toString());
    }

    @Test
    public void testLemmaAndTransitivity() {

        Set<DomainVariable> domainVars = new HashSet<DomainVariable>();
        Set<PropositionalVariable> propsitionalVars = new HashSet<PropositionalVariable>();
        Set<UninterpretedFunction> uninterpretedFunctions = new HashSet<UninterpretedFunction>();
        Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();

        propsitionalVars.add(new PropositionalVariable("a", 1));
        propsitionalVars.add(new PropositionalVariable("b", 2));
        propsitionalVars.add(new PropositionalVariable("c", 3));
        propsitionalVars.add(new PropositionalVariable("d", 3));
        propsitionalVars.add(new PropositionalVariable("e", -1));
        propsitionalVars.add(new PropositionalVariable("f", -1));

        propsitionalVars.add(new PropositionalVariable("x", -1));
        propsitionalVars.add(new PropositionalVariable("y", -1));

        String unitResolution1 = "(|unit-resolution| (hypothesis (not (= x b))) (asserted (or (= b x) (not (= e f)))) (not (= e f)))";
        String unitResolution2 = "(|unit-resolution| (asserted (or (= c d) (= e f)))"
                + unitResolution1 + "(= c d))";
        String unitResolution3 = "(|unit-resolution| " + unitResolution2
                + " (asserted (not (= c d))) false)";
        String lemmaProof = "(lemma " + unitResolution3 + "(= x b))";

        String symmetry = "(symm (asserted (= a y)) (= y a))";
        String trans1 = "(trans (asserted (= a x)) " + lemmaProof + " (= a b))";
        String trans2 = "(trans " + symmetry + trans1 + "(= y b))";

        String proof = "(|unit-resolution| " + trans2
                + "(asserted (not (= y b))) false)";

        String output = parseAndTransform(proof, domainVars, propsitionalVars,
                uninterpretedFunctions, arrayVars);

        String expectedOutput = "( |unit-resolution|{( = y b)} ( |unit-resolution|{( = x b)} ( |unit-resolution|{( = c d)} ( |unit-resolution|{( = e f)} ( asserted ( or ( = c d ) ( = e f ) ) ) ( asserted ( or ( not ( = e f ) ) ( = x b ) ) ) ( or ( = c d ) ( = x b ) ) ) ( asserted ( or ( not ( = c d ) ) ) ) ( or ( = x b ) ) ) ( |unit-resolution|{( = y x)} ( |unit-resolution|{( = a x)} ( asserted ( or ( = a x ) ) ) ( |unit-resolution|{( = y a)} ( asserted ( or ( = y a ) ) ) ( asserted ( or ( not ( = y a ) ) ( not ( = a x ) ) ( = y x ) ) ) ( or ( not ( = a x ) ) ( = y x ) ) ) ( or ( = y x ) ) ) ( asserted ( or ( not ( = y x ) ) ( not ( = x b ) ) ( = y b ) ) ) ( or ( not ( = x b ) ) ( = y b ) ) ) ( or ( = y b ) ) ) ( asserted ( or ( not ( = y b ) ) ) ) ( or false ))";

        Assert.assertEquals(SExpression.fromString(expectedOutput).toString(),
                SExpression.fromString(output).toString());
    }

    @Test
    public void test1ToLocalProof() {

        Set<DomainVariable> domainVars = new HashSet<DomainVariable>();
        Set<PropositionalVariable> propsitionalVars = new HashSet<PropositionalVariable>();
        Set<UninterpretedFunction> uninterpretedFunctions = new HashSet<UninterpretedFunction>();
        Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();

        domainVars.add(new DomainVariable("a", 1));
        domainVars.add(new DomainVariable("b", 2));

        domainVars.add(new DomainVariable("x", -1));
        domainVars.add(new DomainVariable("y", -1));

        uninterpretedFunctions.add(new UninterpretedFunction("f", 1,
                SExpressionConstants.VALUE_TYPE));

        String trans1 = "(trans (asserted (= a x)) (asserted (= x b)) (= a b))";
        String monotonicity1 = "(monotonicity " + trans1 + "(= (f a) (f b)))";
        String symmetrie = "(symm " + monotonicity1 + "(= (f b) (f a)))";
        String trans2 = "(trans " + symmetrie
                + "(asserted (= (f a) y)) (= (f b) y))";

        String proof = "(|unit-resolution| " + trans2
                + "(symm (asserted (not (= y (f b)))) (not (= (f b) y)))"
                + "false)";

        String output = parseAndTransform(proof, domainVars, propsitionalVars,
                uninterpretedFunctions, arrayVars);

        String expectedOutput = "( |unit-resolution|{( = ( f b ) y)} ( |unit-resolution|{( = ( f x ) y)} ( |unit-resolution|{( = ( f a ) y)} ( asserted ( or ( = ( f a ) y ) ) ) ( |unit-resolution|{( = ( f a ) ( f x ))} ( |unit-resolution|{( = a x)} ( asserted ( or ( = a x ) ) ) ( asserted ( or ( not ( = a x ) ) ( = ( f a ) ( f x ) ) ) ) ( or ( = ( f a ) ( f x ) ) ) ) ( asserted ( or ( not ( = ( f x ) ( f a ) ) ) ( not ( = ( f a ) y ) ) ( = ( f x ) y ) ) ) ( or ( not ( = ( f a ) y ) ) ( = ( f x ) y ) ) ) ( or ( = ( f x ) y ) ) ) ( |unit-resolution|{( = ( f x ) ( f b ))} ( |unit-resolution|{( = x b)} ( asserted ( or ( = x b ) ) ) ( asserted ( or ( not ( = x b ) ) ( = ( f x ) ( f b ) ) ) ) ( or ( = ( f x ) ( f b ) ) ) ) ( asserted ( or ( not ( = ( f b ) ( f x ) ) ) ( not ( = ( f x ) y ) ) ( = ( f b ) y ) ) ) ( or ( not ( = ( f x ) y ) ) ( = ( f b ) y ) ) ) ( or ( = ( f b ) y ) ) ) ( asserted ( or ( not ( = ( f b ) y ) ) ) ) ( or false ))";

        Assert.assertEquals(SExpression.fromString(expectedOutput).toString(),
                SExpression.fromString(output).toString());
    }

    @Test
    public void test2ToLocalProof() {

        Set<DomainVariable> domainVars = new HashSet<DomainVariable>();
        Set<PropositionalVariable> propsitionalVars = new HashSet<PropositionalVariable>();
        Set<UninterpretedFunction> uninterpretedFunctions = new HashSet<UninterpretedFunction>();
        Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();

        domainVars.add(new DomainVariable("a", 1));
        domainVars.add(new DomainVariable("b", 1));

        domainVars.add(new DomainVariable("c", 2));
        domainVars.add(new DomainVariable("d", 2));

        domainVars.add(new DomainVariable("x", -1));
        domainVars.add(new DomainVariable("y", -1));
        domainVars.add(new DomainVariable("z", -1));
        domainVars.add(new DomainVariable("u", -1));
        domainVars.add(new DomainVariable("v", -1));
        domainVars.add(new DomainVariable("w", -1));

        uninterpretedFunctions.add(new UninterpretedFunction("f", 2,
                SExpressionConstants.VALUE_TYPE));

        String trans1 = "(trans (asserted (= a x)) (asserted (= x c)) (= a c))";
        String trans2 = "(trans (asserted (= b y)) (asserted (= y d)) (= b d))";

        String mono1 = "(monotonicity " + trans1 + trans2
                + " (= (f a b) (f c d)))";
        String trans3 = "(trans (asserted (= u (f a b))) " + mono1
                + " (= u (f c d)))";

        String sym1 = "(symm " + trans3 + " (= (f c d) u))";

        String trans4 = "(trans " + sym1 + " (asserted (= u v)) (= (f c d) v))";

        String sym2 = "(symm " + trans4 + " (= v (f c d)))";

        String proof = "(|unit-resolution| " + sym2
                + " (asserted (not (= v (f c d)))) false)";

        String output = parseAndTransform(proof, domainVars, propsitionalVars,
                uninterpretedFunctions, arrayVars);

        String expectedOutput = "( |unit-resolution|{( = v ( f c d ))} ( |unit-resolution|{( = ( f x y ) ( f c d ))} ( |unit-resolution|{( = y d)} ( asserted ( or ( = y d ) ) ) ( |unit-resolution|{( = x c)} ( asserted ( or ( = x c ) ) ) ( asserted ( or ( not ( = x c ) ) ( not ( = y d ) ) ( = ( f x y ) ( f c d ) ) ) ) ( or ( not ( = y d ) ) ( = ( f x y ) ( f c d ) ) ) ) ( or ( = ( f x y ) ( f c d ) ) ) ) ( |unit-resolution|{( = ( f x y ) v)} ( |unit-resolution|{( = u v)} ( asserted ( or ( = u v ) ) ) ( |unit-resolution|{( = u ( f x y ))} ( |unit-resolution|{( = ( f a b ) ( f x y ))} ( |unit-resolution|{( = b y)} ( asserted ( or ( = b y ) ) ) ( |unit-resolution|{( = a x)} ( asserted ( or ( = a x ) ) ) ( asserted ( or ( not ( = a x ) ) ( not ( = b y ) ) ( = ( f a b ) ( f x y ) ) ) ) ( or ( not ( = b y ) ) ( = ( f a b ) ( f x y ) ) ) ) ( or ( = ( f a b ) ( f x y ) ) ) ) ( |unit-resolution|{( = u ( f a b ))} ( asserted ( or ( = u ( f a b ) ) ) ) ( asserted ( or ( not ( = u ( f a b ) ) ) ( not ( = ( f a b ) ( f x y ) ) ) ( = u ( f x y ) ) ) ) ( or ( not ( = ( f a b ) ( f x y ) ) ) ( = u ( f x y ) ) ) ) ( or ( = u ( f x y ) ) ) ) ( asserted ( or ( not ( = ( f x y ) u ) ) ( not ( = u v ) ) ( = ( f x y ) v ) ) ) ( or ( not ( = u v ) ) ( = ( f x y ) v ) ) ) ( or ( = ( f x y ) v ) ) ) ( asserted ( or ( not ( = v ( f x y ) ) ) ( not ( = ( f x y ) ( f c d ) ) ) ( = v ( f c d ) ) ) ) ( or ( not ( = ( f x y ) ( f c d ) ) ) ( = v ( f c d ) ) ) ) ( or ( = v ( f c d ) ) ) ) ( asserted ( or ( not ( = v ( f c d ) ) ) ) ) ( or false ))";

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
            exc.printStackTrace();
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
            exc.printStackTrace();
            throw new RuntimeException("Proof Parse Error in Testcase: " + exc);
        }

        Z3Proof rootProof = proofParser.getRootProof();
        @SuppressWarnings("unused")
        String proofString = rootProof.prettyPrint();
        Assert.assertTrue(rootProof.checkZ3ProofNode());

        rootProof.localLemmasToAssertions();
        Assert.assertTrue(rootProof.checkZ3ProofNode());
        rootProof.removeLocalSubProofs();
        Assert.assertTrue(rootProof.checkZ3ProofNode());
        rootProof.dealWithModusPonens();
        Assert.assertTrue(rootProof.checkZ3ProofNode());
        TransformedZ3Proof transformedZ3Proof = TransformedZ3Proof
                .convertToTransformedZ3Proof(rootProof);
        Assert.assertTrue(transformedZ3Proof.checkZ3ProofNode());
        transformedZ3Proof.toLocalProof();
        Assert.assertTrue(transformedZ3Proof.checkZ3ProofNode());
        transformedZ3Proof.toResolutionProof();
        Assert.assertTrue(transformedZ3Proof.checkZ3ProofNode());
        @SuppressWarnings("unused")
        String test = transformedZ3Proof.prettyPrint();

        // START: ASHUTOSH code
        ResProof resolutionProof = Util
                .createResolutionProof(transformedZ3Proof);
        resolutionProof.checkProof(false);
        resolutionProof.rmDoubleLits();
        resolutionProof.checkProof(false);
        resolutionProof.deLocalizeProof();
        resolutionProof.checkProof(false);
        // END: ASHUTOSH code

        return transformedZ3Proof.toString().replaceAll("\n", "")
                .replaceAll("\\s{2,}", " ");
    }
}