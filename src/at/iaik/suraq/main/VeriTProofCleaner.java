/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.main;

import java.util.HashSet;
import java.util.Set;

import at.iaik.suraq.proof.VeritProof;
import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.smtlib.formula.Formula;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class VeriTProofCleaner {

    /**
     * The proof to clean
     */
    private final VeritProof proof;

    /**
     * 
     * Constructs a new <code>VeriTProofCleaner</code>.
     * 
     * @param proof
     *            the proof to clean
     */
    public VeriTProofCleaner(VeritProof proof) {
        this.proof = proof;
    }

    /**
     * Cleans the proof of bad literals
     */
    public void cleanProof() {
        VeritProofNode currentLeaf = proof.getOneGoodDefinitionOfBadLiteral();
        while (currentLeaf != null) {
            cleanProof(currentLeaf);
            assert (!proof.getProofNodes().contains(currentLeaf));
            assert (!proof.getGoodDefinitionsOfBadLiterals().contains(
                    currentLeaf));
            currentLeaf = proof.getOneGoodDefinitionOfBadLiteral();
        }
        assert (proof.isClean());
        assert (proof.checkProof());
    }

    /**
     * Rewrites the proof to get rid of the given bad literal definition.
     * 
     * @param currentLeaf
     *            a good definition of a bad literal
     */
    private void cleanProof(VeritProofNode currentLeaf) {
        assert (currentLeaf.isLeaf());
        assert (currentLeaf.isGoodDefinitionOfBadLiteral());

        Formula badLiteral = currentLeaf.getDefinedBadLiteral();
        assert (badLiteral != null);

        Set<Formula> resolvedDefiningLiterals = new HashSet<Formula>();

        // TODO
        // Search for resolution of bad literal
        // Record path

        // TODO
        // Record which definition literals are resolved along the path

        // TODO
        // Go back up the other way

        // TODO
        // Change nodes along the way

    }

    /**
     * @return the <code>proof</code>
     */
    public VeritProof getProof() {
        return proof;
    }

}
