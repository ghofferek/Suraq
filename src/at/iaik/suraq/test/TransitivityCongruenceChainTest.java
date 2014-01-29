/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.util.Set;

import org.junit.After;
import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.main.Suraq;
import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.proof.VeritProof;
import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.util.FormulaCache;
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
        FormulaCache.clearAll();
    }

    private void testNode(String pathToInputFile, String pathToProofFile,
            String nodeName) throws FileNotFoundException {
        testNode(pathToInputFile, pathToProofFile, nodeName, false);
    }

    private void testNode(String pathToInputFile, String pathToProofFile,
            String nodeName, boolean isPredicateNode)
            throws FileNotFoundException {
        String[] args = { "-i", pathToInputFile, "--tseitin", "1", "--solver",
                "verit" };
        Suraq suraq = new Suraq(args);

        BufferedReader proofReader = new BufferedReader(new FileReader(
                new File(pathToProofFile)));

        VeritProof proof = suraq
                .justDoInputTransformationAndThenParseThisProofFile(proofReader);
        VeritProofNode node = proof.getProofNode(nodeName);

        VeritProofNode colorableNode = null;
        if (isPredicateNode) {
            colorableNode = node.splitPredicateLeafNew();
        } else {
            TransitivityCongruenceChain chain = TransitivityCongruenceChain
                    .create(node);
            colorableNode = chain.toColorableProofNew();
        }
        Assert.assertNotNull(colorableNode);

        Assert.assertTrue(
                "Unexpected literal in node.",
                node.getLiteralConclusions().containsAll(
                        colorableNode.getLiteralConclusions()));

        for (VeritProofNode leaf : colorableNode.getLeaves()) {
            Assert.assertTrue("Leaf not colorable", leaf.isColorable());
        }

        Assert.assertTrue("Node not correct", colorableNode.checkProofNode());

    }

    private void testAllNodes(String pathToInputFile, String pathToProofFile)
            throws FileNotFoundException {
        String[] args = { "-i", pathToInputFile, "--tseitin", "1", "--solver",
                "verit" };
        Suraq suraq = new Suraq(args);

        BufferedReader proofReader = new BufferedReader(new FileReader(
                new File(pathToProofFile)));

        VeritProof proof = suraq
                .justDoInputTransformationAndThenParseThisProofFile(proofReader);

        proof.removeUnreachableNodes();
        Set<VeritProofNode> leaves = proof.getLeaves();

        for (VeritProofNode node : leaves) {
            if (node.isColorable())
                continue;

            Util.printToSystemOutWithWallClockTimePrefix("Splitting leaf "
                    + node.getName());

            VeritProofNode colorableNode = null;
            if (Util.getImpliedLiteral(node.getLiteralConclusions()) instanceof UninterpretedPredicateInstance) {
                colorableNode = node.splitPredicateLeafNew();
            } else {
                TransitivityCongruenceChain chain = TransitivityCongruenceChain
                        .create(node);
                colorableNode = chain.toColorableProofNew();
            }
            Assert.assertNotNull(colorableNode);

            Assert.assertTrue(
                    "Unexpected literal in node.",
                    node.getLiteralConclusions().containsAll(
                            colorableNode.getLiteralConclusions()));

            for (VeritProofNode leaf : colorableNode.getLeaves()) {
                Assert.assertTrue("Leaf not colorable", leaf.isColorable());
            }

            Assert.assertTrue("Node not correct",
                    colorableNode.checkProofNode());
        }
    }

    @Test
    public void testAllNodesFromSimpleProcessor() throws FileNotFoundException {
        testAllNodes("./rsc/test/simple_processor.smt2",
                "./rsc/dbg/simple_processor_proof.smt2");
    }

    /**
     * Tests splitting of node c265808 from dlx_2_controller_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec265808() throws FileNotFoundException {
        testNode("./rsc/dlx/dlx_no_domainITE_2_controllers.smt2",
                "./rsc/dbg/c265808.smt2", ".c265808");
    }

    /**
     * Tests splitting of node c245868 from dlx_2_controller_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec245868() throws FileNotFoundException {
        testNode("./rsc/dlx/dlx_no_domainITE_2_controllers.smt2",
                "./rsc/dbg/c245868.smt2", ".c245868");
    }

    /**
     * Tests splitting of node c87503 from dlx_2_controller_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec87503() throws FileNotFoundException {
        testNode("./rsc/dlx/dlx_no_domainITE_2_controllers.smt2",
                "./rsc/dbg/c87503.smt2", ".c87503");
    }

    /**
     * Tests splitting of node c63143 from dlx_2_controller_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec63143() throws FileNotFoundException {
        testNode("./rsc/dlx/dlx_no_domainITE_2_controllers.smt2",
                "./rsc/dbg/c63143.smt2", ".c63143", true);
    }

    /**
     * Tests splitting of node c63078 from dlx_2_controller_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec63078() throws FileNotFoundException {
        testNode("./rsc/dlx/dlx_no_domainITE_2_controllers.smt2",
                "./rsc/dbg/c63078.smt2", ".c63078", true);
    }

    /**
     * Tests splitting of node c217742 from dlx_2_controller_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec224365() throws FileNotFoundException {
        testNode("./rsc/dlx/dlx_no_domainITE_2_controllers.smt2",
                "./rsc/dbg/c224365.smt2", ".c224365");
    }

    /**
     * Tests splitting of node c217742 from dlx_2_controller_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec217742() throws FileNotFoundException {
        testNode("./rsc/dlx/dlx_no_domainITE_2_controllers.smt2",
                "./rsc/dbg/c217742.smt2", ".c217742");
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
     * Tests splitting of node c213298 from dlx_2_controller_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec213298() throws FileNotFoundException {
        testNode("./rsc/dlx/dlx_no_domainITE_2_controllers.smt2",
                "./rsc/dbg/c213298.smt2", ".c213298");
    }

    /**
     * Tests splitting of node c132457 from dlx_2_controller_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec70150() throws FileNotFoundException {
        testNode("./rsc/dlx/dlx_no_domainITE_2_controllers.smt2",
                "./rsc/dbg/c70150.smt2", ".c70150");
    }

    /**
     * Tests splitting of node c219182 from dlx_2_controller_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec219182() throws FileNotFoundException {
        testNode("./rsc/dlx/dlx_no_domainITE_2_controllers.smt2",
                "./rsc/dbg/c219182.smt2", ".c219182");
    }

    /**
     * Tests splitting of node c135311 from dlx_2_controller_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec135311() throws FileNotFoundException {
        testNode("./rsc/dlx/dlx_no_domainITE_2_controllers.smt2",
                "./rsc/dbg/c135311.smt2", ".c135311");
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

    /**
     * Tests splitting of predicate node c1353 from simple_processor_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec1353() throws FileNotFoundException {
        testNode("./rsc/test/simple_processor.smt2", "./rsc/dbg/c1353.smt2",
                ".c1353", true);
    }

    /**
     * Tests splitting of predicate node c1148 from simple_processor_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec1148() throws FileNotFoundException {
        testNode("./rsc/test/simple_processor.smt2", "./rsc/dbg/c1148.smt2",
                ".c1148", true);
    }

}
