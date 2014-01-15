/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;

import org.junit.After;
import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.main.Suraq;
import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.proof.VeritProof;
import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.util.Util;
import at.iaik.suraq.util.chain.TransitivityCongruenceChain;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TransitivityCongruenceChainTest {

    /**
     * Performs necessary resets to run multiple tests.
     */
    @After
    public void tearDown() {
        SuraqOptions.kill();
        Util.resetTseitinCounter();
    }

    private void testNode(String pathToInputFile, String pathToProofFile,
            String nodeName) throws FileNotFoundException {
        String[] args = { "-i", pathToInputFile, "--tseitin", "1", "--solver",
                "verit" };
        Suraq suraq = new Suraq(args);

        BufferedReader proofReader = new BufferedReader(new FileReader(
                new File(pathToProofFile)));

        VeritProof proof = suraq
                .justDoInputTransformationAndThenParseThisProofFile(proofReader);
        VeritProofNode node = proof.getProofNode(nodeName);

        TransitivityCongruenceChain chain = TransitivityCongruenceChain
                .create(node);
        VeritProofNode colorableNode = chain.toColorableProofNew();

        Assert.assertTrue(
                "Unexpected literal in node.",
                node.getLiteralConclusions().containsAll(
                        colorableNode.getLiteralConclusions()));

        for (VeritProofNode leaf : colorableNode.getLeaves()) {
            Assert.assertTrue("Leaf not colorable", leaf.isColorable());
        }

        Assert.assertTrue("Node not correct", colorableNode.checkProofNode());

    }

    /**
     * Tests splitting of node c132457 from dlx_2_controller_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec132457() throws FileNotFoundException {
        testNode("./rsc/dlx/dlx_no_domainITE_2_controllers.smt2",
                "./rsc/dbg/c132457.smt2", ".c132457");
    }

    /**
     * Tests splitting of node c1456 from simple_processor_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec1456() throws FileNotFoundException {
        testNode("./rsc/test/simple_processor.smt2", "./rsc/dbg/c1456.smt2",
                ".c1456");
    }
}
