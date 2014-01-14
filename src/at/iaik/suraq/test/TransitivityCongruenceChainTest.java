/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.test;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;

import org.junit.Assert;
import org.junit.Test;

import at.iaik.suraq.main.Suraq;
import at.iaik.suraq.proof.VeritProof;
import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.util.chain.TransitivityCongruenceChain;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TransitivityCongruenceChainTest {

    /**
     * Tests splitting of node c132457 from dlx_2_controller_proof.
     * 
     * @throws FileNotFoundException
     */
    @Test
    public void testNodec132457() throws FileNotFoundException {

        String[] args = { "-i",
                "./rsc/dlx/dlx_no_domainITE_2_controllers.smt2", "--tseitin",
                "1", "--solver", "verit" };
        Suraq suraq = new Suraq(args);

        BufferedReader proofReader = new BufferedReader(new FileReader(
                new File("./rsc/dbg/c132457.smt2")));

        VeritProof proof = suraq
                .justDoInputTransformationAndThenParseThisProofFile(proofReader);
        VeritProofNode node = proof.getProofNode(".c132457");

        TransitivityCongruenceChain chain = TransitivityCongruenceChain
                .create(node);
        VeritProofNode colorableNode = chain.toColorableProofNew();

        Assert.assertTrue("Node not colorable", colorableNode.isColorable());

        for (VeritProofNode leaf : proof.getLeaves()) {
            Assert.assertTrue("Leaf not colorable", leaf.isColorable());
        }

        Assert.assertTrue("Node not correct", colorableNode.checkProofNode());
    }
}
