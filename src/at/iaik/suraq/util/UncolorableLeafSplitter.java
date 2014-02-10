/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.util.chain.TransitivityCongruenceChain;

/**
 * For parallel splitting of uncolorable leaves.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class UncolorableLeafSplitter implements Runnable {

    /**
     * An identifying integer among all leaf-splitters.
     */
    private final int id;

    /**
     * The leaves to be split by this splitter.
     */
    private final List<VeritProofNode> leavesToSplit;

    /**
     * The map from original nodes to replaced nodes.
     */
    private final Map<VeritProofNode, VeritProofNode> replacements;

    /**
     * Counts how many literals were saved by this splitter
     */
    private int totalLiteralsFewer = 0;

    /**
     * Counts how many clauses were being made stronger by this splitter.
     */
    private int numStrongerClauses = 0;

    /**
     * Stores whether everything went right
     */
    private boolean allOk = false;

    /**
     * 
     * Constructs a new <code>UncolorableLeafSplitter</code>.
     * 
     * @param id
     * @param leavesToSplit
     */
    public UncolorableLeafSplitter(int id, List<VeritProofNode> leavesToSplit) {
        this.id = id;
        this.leavesToSplit = new ArrayList<VeritProofNode>(leavesToSplit);
        this.replacements = new HashMap<VeritProofNode, VeritProofNode>(
                leavesToSplit.size());
    }

    /**
     * @see java.lang.Runnable#run()
     */
    @Override
    public void run() {
        try {
            split();
            allOk = true;
        } catch (Throwable exc) {
            Util.printToSystemOutWithWallClockTimePrefix("Exception in Splitter "
                    + id + ". Stacktrace follows.");
            exc.printStackTrace();
            allOk = false;
        }
    }

    /**
     * Performs the actual work
     */
    private synchronized void split() {

        int count = 0;
        while (!leavesToSplit.isEmpty()) {
            VeritProofNode leafToSplit = leavesToSplit.remove(leavesToSplit
                    .size() - 1);

            assert (CongruenceClosure.checkVeritProofNode(leafToSplit));
            assert (Util.countPositiveLiterals(leafToSplit
                    .getLiteralConclusions()) == 1);
            assert (Util.countPositiveLiterals(leafToSplit
                    .getLiteralConclusions())
                    + Util.countNegativeLiterals(leafToSplit
                            .getLiteralConclusions()) == leafToSplit
                    .getLiteralConclusions().size());

            Formula positiveLiteral = Util.findPositiveLiteral(leafToSplit
                    .getLiteralConclusions());
            assert (positiveLiteral != null);
            assert (positiveLiteral instanceof DomainEq || positiveLiteral instanceof UninterpretedPredicateInstance);

            VeritProofNode replacement = null;
            // if (leafToClean.getType().equals(VeriTToken.EQ_CONGRUENT)
            // || leafToClean.getType().equals(VeriTToken.EQ_TRANSITIVE)) {
            if (positiveLiteral instanceof DomainEq) {
                Util.printToSystemOutWithWallClockTimePrefix("    "
                        + "Splitter " + id + ": " + "Splitting leaf "
                        + leafToSplit.getName());
                TransitivityCongruenceChain chain = TransitivityCongruenceChain
                        .create(leafToSplit);
                replacement = chain.toColorableProofNew();
                // } else if (leafToClean.getType().equals(
                // VeriTToken.EQ_CONGRUENT_PRED)) {
            } else if (positiveLiteral instanceof UninterpretedPredicateInstance) {
                Util.printToSystemOutWithWallClockTimePrefix("    "
                        + "Splitter " + id + ": "
                        + "Splitting (predicate) leaf " + leafToSplit.getName());
                replacement = leafToSplit.splitPredicateLeafNew();
            } else {
                Util.printToSystemOutWithWallClockTimePrefix("    "
                        + "Splitter " + id + ": "
                        + "Unexpected implied literal:");
                System.out.println(positiveLiteral.toString());
                System.out.println("Containing leaf:");
                System.out.println(leafToSplit.toString());
                assert (false);
            }
            assert (replacement != null);
            assert (leafToSplit.getLiteralConclusions().containsAll(replacement
                    .getLiteralConclusions()));
            int difference = leafToSplit.getLiteralConclusions().size()
                    - replacement.getLiteralConclusions().size();
            assert (difference >= 0);
            if (difference > 0) {
                totalLiteralsFewer += difference;
                numStrongerClauses++;
                Util.printToSystemOutWithWallClockTimePrefix("    "
                        + "Splitter " + id + ": " + "Replacement has "
                        + replacement.getLiteralConclusions().size()
                        + " literals (" + difference
                        + " literals fewer than original leaf.)");
            } else
                Util.printToSystemOutWithWallClockTimePrefix("    "
                        + "Splitter " + id + ": "
                        + "Replacement has the same number of literals. ("
                        + replacement.getLiteralConclusions().size() + ")");
            Util.printToSystemOutWithWallClockTimePrefix("    " + "Splitter "
                    + id + ": " + totalLiteralsFewer
                    + " literals saved so far in " + numStrongerClauses
                    + " clauses.");
            replacements.put(leafToSplit, replacement);
            Util.printToSystemOutWithWallClockTimePrefix("    " + "Splitter "
                    + id + ": " + "Done " + ++count + ". ("
                    + leavesToSplit.size() + " remaining.)");
        }
        Util.printToSystemOutWithWallClockTimePrefix("    " + "Splitter " + id
                + ": " + "All done.");
        Util.printToSystemOutWithWallClockTimePrefix("Splitter " + id + ": "
                + totalLiteralsFewer + " literals saved in total.");
    }

    /**
     * 
     * @return <code>true</code> iff splitting was performed successfully.
     */
    public synchronized boolean isAllOk() {
        return allOk;
    }

    /**
     * 
     * @return the number of literals saved by this splitter.
     */
    public synchronized int getTotalLiteralsFewer() {
        return totalLiteralsFewer;
    }

    /**
     * 
     * @return the number of clauses made stronger by this splitter.
     */
    public synchronized int getNumStrongerClauses() {
        return numStrongerClauses;
    }

    /**
     * 
     * @return the replacements for the leaves split by this splitter (copy).
     */
    public synchronized Map<VeritProofNode, VeritProofNode> getReplacements() {
        Map<VeritProofNode, VeritProofNode> result = new HashMap<VeritProofNode, VeritProofNode>(
                replacements);
        return result;
    }

}
