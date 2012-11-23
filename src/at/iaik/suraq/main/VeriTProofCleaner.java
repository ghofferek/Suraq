/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.main;

import at.iaik.suraq.proof.VeritProof;

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
        // TODO
    }

    /**
     * @return the <code>proof</code>
     */
    public VeritProof getProof() {
        return proof;
    }

}
