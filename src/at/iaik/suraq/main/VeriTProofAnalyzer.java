/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.main;

import java.io.File;
import java.io.FileWriter;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.proof.VeritProof;
import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.util.Util;

/**
 * EXPERIMENTAL Class to deal with BadLiterals in VeriTProofs
 * 
 * @author chillebold
 * 
 */
@Deprecated
public class VeriTProofAnalyzer {
    /**
     * The internal stored proof, set by the constructor.
     */
    private final VeritProof proof;

    /**
     * Public Constructor, stores the proof internally
     * 
     * @param proof
     */
    public VeriTProofAnalyzer(VeritProof proof) {
        this.proof = proof;
    }

    /**
     * This method tries to remove Bad literals from the proof. It only calles
     * VeriTProofAnalyzer.removeBadLiteralsTransitive(...) in a loop.
     */
    public void removeBadLiterals() {

        // removes bad literals as long as we were able to remove any.
        // The removeBadLiteralsTransitive(null) does all the work.
        // The rest is only for debugging issues.
        // You can filter, what you want to remove by giving a Type instead of
        // null
        // As an example see the blocks beneath the following block.
        {
            System.out.println(">> removeBadLiterals (NULL): proof-size: "
                    + proof.getProofNodes().size() + " literals:"
                    + proof.getLiteralConclusionsCount() + " bad: "
                    + this.findBadLiterals(true).size() + " <<");
            while (removeBadLiteralsTransitive(null)) {
                System.out.println(">> removeBadLiterals (NULL): proof-size: "
                        + proof.getProofNodes().size() + " literals:"
                        + proof.getLiteralConclusionsCount() + " bad: "
                        + this.findBadLiterals(true).size() + " <<");
            }
        }

        // Removes bad literals but only TRANSITIVITIES
        /*
         * { System.out.println(">> removeBadLiterals (TRANS): proof-size: " +
         * proof.getProofNodes().size() + " literals:" +
         * proof.getLiteralConclusionsCount() + " bad: " +
         * this.findBadLiterals(true).size() + " <<"); while
         * (removeBadLiteralsTransitive(VeriTToken.EQ_TRANSITIVE)) {
         * System.out.println(">> removeBadLiterals (TRANS): proof-size: " +
         * proof.getProofNodes().size() + " literals:" +
         * proof.getLiteralConclusionsCount() + " bad: " +
         * this.findBadLiterals(true).size() + " <<"); } }
         */

        // Removes bad literals but only CONGRUENCES
        /*
         * { System.out.println(">> removeBadLiterals (CONGR): proof-size: " +
         * proof.getProofNodes().size() + " literals:" +
         * proof.getLiteralConclusionsCount() + " bad: " +
         * this.findBadLiterals(true).size() + " <<"); while
         * (removeBadLiteralsTransitive(VeriTToken.EQ_CONGRUENT)) {
         * System.out.println(">> removeBadLiterals (CONGR): proof-size: " +
         * proof.getProofNodes().size() + " literals:" +
         * proof.getLiteralConclusionsCount() + " bad: " +
         * this.findBadLiterals(true).size() + " <<"); } }
         */
    }

    /**
     * Removes bad literals if we can do so.
     * 
     * @param type
     *            filter: which type of ProofNodes shall be removed? null if we
     *            should not filter.
     * @return
     */
    private boolean removeBadLiteralsTransitive(Token type) {

        // in the first step, we only look for eq_transitive and eq_congruent,
        // which only occurs as leafs (no subProofs)
        // Set<Formula> badLiterals = this.findBadLiterals(false);
        // Hashtable<Formula, List<VeritProofNode>> badLiterals =
        // findBadLiteralsWithProofNode(false);

        // VeriTProofNode: The ProofNode where the implication is defined
        // AbstractMap.SimpleEntry: PlaceHolder to Store two Elements:
        // - Formula and
        // - a List of Formulas

        // Example:
        // a ^ b ^ c => d is the same as:
        // !a v !b v !c v d (because of that, I call it implications)
        // ---------------------------------------------------------
        // the Formula is: d
        // The list of Formulas is: [!a, !b, !c]
        // The VeritProofNode is the node, where the badLiteral occurs without
        // Children and defines something like the example
        Hashtable<VeritProofNode, AbstractMap.SimpleEntry<Formula, List<Formula>>> implications = findImplicationDefinitionsWithBadLiteralsOnlyinPositiveForm(
                false, type);
        System.out
                .println("\n Found "
                        + implications.size()
                        + " bad literals with no subProofs that only had bad literals in the positive form.");

        // Iterate over all badLiterals (They have no subProofs)
        for (VeritProofNode start_node : implications.keySet()) {
            Formula badLiteral = implications.get(start_node).getKey();
            List<Formula> conditions = implications.get(start_node).getValue();

            // ignore if we got something with subProofs
            if (start_node.getSubProofs() != null) {
                continue;
            }

            // System.out.print(start_node.getName()+"("+start_node.getType()+"): ");

            // 1. propagate to the parents till the (positive) badLiteral
            // vanishes
            List<VeritProofNode> ends = new ArrayList<VeritProofNode>();
            replaceBadLiteralToParents(start_node, conditions, badLiteral, ends);

            // remove the start_node from the temporary ends-list.
            ends.remove(start_node);
            // System.out.print("  Ends: "+ends.size()+". ");

            // 2. propagate to the children till the (negative) badLiteral
            // vanishes
            // TODO: split the result in several steps
            NotFormula negatedBadLiteral = NotFormula.create(badLiteral);
            for (VeritProofNode end : ends) {
                replaceBadLiteralToSubProofs(end, conditions, negatedBadLiteral);
            }

            // 3. delete current node from proof
            proof.removeProofSet(start_node);
        }
        return implications.size() > 0;
    }

    /**
     * Gets a List of Formulas, if there are NotFormulas inside, they are
     * removed.
     * 
     * @param formulas
     *            a list of negated Formulas (still positive if they was
     *            positive)
     * @return a list of positive Formulas
     */
    private List<Formula> removeNotFormulas(List<Formula> formulas) {
        ArrayList<Formula> tmp = new ArrayList<Formula>();
        for (Formula formula : formulas) {
            if (formula instanceof NotFormula)
                tmp.add(((NotFormula) formula).getNegatedFormula());
            else
                tmp.add(formula);
        }
        return tmp;
    }

    /**
     * Propagate to the subProofs (children)
     * 
     * @param node
     *            The node to start
     * @param conditions
     *            conditions in negated form
     * @param badLiteral
     *            badLiteral in negated form
     */
    private void replaceBadLiteralToSubProofs(VeritProofNode node,
            List<Formula> conditions, Formula badLiteral) {
        if (node.getSubProofs() == null) {
            // System.out.print('0');
            return;
        }

        // Formula badLiteralPositive =
        // ((NotFormula)badLiteral).getNegatedFormula();

        // System.out.print('(');
        for (VeritProofNode child : node.getSubProofs()) {
            // following command does NOT return a copy!!!
            // so we can modify the list directly
            List<Formula> formulas = child.getLiteralConclusions(); // no copy!
            int index = formulas.indexOf(badLiteral);
            if (index == -1) {
                // the badLiteral does not occur any more :-)
            } else {
                // System.out.print('-');
                assert (formulas.remove(badLiteral)); // :-)
                formulas.addAll(conditions);
                replaceBadLiteralToSubProofs(child, conditions, badLiteral);
            }

            // if(formulas.contains(badLiteralPositive))
            // we have reached e.g. an other EQ_TRANSITIVE, that also defines
            // this badLiteral
        }
        // System.out.print(')');
    }

    /**
     * Propagate to the Parents
     * 
     * @param node
     *            Node to start with
     * @param conditions
     *            conditions in negated Form
     * @param badLiteral
     *            badLiteral in positive Form
     * @param ends
     */
    private void replaceBadLiteralToParents(VeritProofNode node,
            List<Formula> conditions, Formula badLiteral,
            List<VeritProofNode> ends) {
        // badLiteral is in Positive Form, conditions are in Negated Form
        if (node.getParents() == null) {
            // System.out.print(node.getName()+".");
            ends.add(node);
            return;
        }
        // NotFormula badLiteralNegative = NotFormula.create(badLiteral);

        // System.out.print('(');
        for (VeritProofNode parent : node.getParents()) {
            // following IS ALLOWED, the node could already be removed from the
            // proof
            // assert(parent.getSubProofs().contains(node));

            List<Formula> formulas = parent.getLiteralConclusions(); // no copy!
            int position = formulas.indexOf(badLiteral);
            if (position != -1) {
                if (conditions.size() == 1) {
                    // unfortunately never occurs
                    System.out.print('/');
                    formulas.set(position, removeNotFormulas(conditions).get(0));
                    replaceBadLiteralToParents(parent, conditions, badLiteral,
                            ends);
                } else {
                    // badLiteral is contained in in positive form
                    if (node.getLiteralConclusions().containsAll(
                            parent.getLiteralConclusions())
                            && parent.getLiteralConclusions().containsAll(
                                    node.getLiteralConclusions()))
                    // if(node.getLiteralConclusions().equals(parent.getLiteralConclusions()))
                    {
                        if (parent.getLiteralConclusions().containsAll(
                                conditions)
                                && parent.getLiteralConclusions().contains(
                                        badLiteral)) {
                            // also delete this node, because it is the same as
                            // the one we want to replace
                            // this is probably of type 'conclusion'
                            this.proof.removeProofSet(parent);
                        } else {
                            // does not occur
                            System.out.print('?');
                        }
                    } else {
                        System.out.print('+');
                        // just testing how much remains
                        // formulas.remove(position);

                        formulas.set(position, AndFormula
                                .generate(removeNotFormulas(conditions)));
                    }

                    replaceBadLiteralToParents(parent, conditions, badLiteral,
                            ends);
                }
            } else {
                // we have reached the end of the down-propagation
                // System.out.print(parent.getName()+",");
                ends.add(parent);
            }

            // should not occur and does not occur :-)
            // if(formulas.contains(badLiteralNegative))
            // throw new RuntimeException("Unexpected but not bad #2");
        }
        // System.out.print(')');
    }

    /**
     * Prints some statistics about badLiterals into a file.
     * 
     * @param fileBadLiterals
     *            file to print the statistics.
     */
    public void analyzeBadLiteralsSat(File fileBadLiterals) {

        Set<Formula> badLiterals = findBadLiterals(false);
        System.out.println("\nThere were " + badLiterals.size()
                + " unique bad literals. Hash: " + badLiterals.hashCode());

        // remove badLiterals, that are once positive and once negative defined.
        // keep badLiterals that are no Literals!
        Set<Formula> badLiterals2 = satisfyBadLiterals(badLiterals);
        System.out
                .println("There were "
                        + badLiterals2.size()
                        + " bad literals after satisfying positive-negative ones. Hash: "
                        + badLiterals2.hashCode());

        if (badLiterals2.size() != 0) {
            int literals = 0;
            int noliterals = 0;
            for (Formula badLiteral : badLiterals2) {
                if (Util.isLiteral(badLiteral))
                    literals++;
                else
                    noliterals++;
            }
            System.err.println("These bad literals were " + literals
                    + " literals and " + noliterals + " not literals.");
        }

        try {
            System.out.println("Writing bad literals to file: "
                    + fileBadLiterals);
            FileWriter fstream = new FileWriter(fileBadLiterals);
            for (Formula badLiteral : badLiterals) {
                fstream.write("\n--------------------------------\n");
                fstream.write(badLiteral.toString());
            }
            fstream.close();
        } catch (Exception ex) {
            throw new RuntimeException(ex);
        }
    }

    /**
     * ONLY FOR DEBUG & STATISTICS. Returns badLiterals that are "no literals"
     * and negative bad literals that does not occur as positive bad literals
     * somewhere
     * 
     * @param badLiterals
     * @return badLiterals that are "no literals" and negative bad literals that
     *         does not occur as positive bad literals somewhere
     */
    public Set<Formula> satisfyBadLiterals(Set<Formula> badLiterals) {
        Set<Formula> filteredBadLiterals = new HashSet<Formula>();
        int positiveElements = 0;
        Set<Formula> veryBadLiterals = new HashSet<Formula>();
        for (Formula badLiteral : badLiterals) {
            if (badLiteral instanceof NotFormula) {
                filteredBadLiterals.add(Util.makeLiteralPositive(badLiteral));
            } else if (!Util.isLiteral(badLiteral)) {
                // very bad "literals"!!!
                if (badLiteral instanceof NotFormula) {
                    filteredBadLiterals.add(((NotFormula) badLiteral)
                            .getNegatedFormula());
                } else
                    veryBadLiterals.add(badLiteral);
            } else
                positiveElements++;
            // else: that's ok
        }
        System.out.println("  removed " + positiveElements
                + " elements because they were positive");

        // filteredBadLiterals are positive now
        int removed_elements = 0;
        int not_removed_elements = 0;
        for (Formula badLiteral : badLiterals) {
            if (filteredBadLiterals.remove(badLiteral))
                removed_elements++;
            else if (!(badLiteral instanceof NotFormula))
                not_removed_elements++;
        }
        System.out.println("  removed " + removed_elements
                + " elements on filtering and " + not_removed_elements
                + " were not to remove.");

        System.out.println("  There were " + veryBadLiterals.size()
                + " Literals, that were no literals and no NOT-formula");
        filteredBadLiterals.addAll(veryBadLiterals);
        return filteredBadLiterals;
    }

    /**
     * Finds bad literals and stores to each one, in which nodes it occured
     * 
     * @param areSubproofsAllowed
     *            defines if found elements may contain subproofs
     * @return
     */
    public Hashtable<Formula, List<VeritProofNode>> findBadLiteralsWithProofNode(
            boolean areSubproofsAllowed) {
        Hashtable<Formula, List<VeritProofNode>> badLiterals = new Hashtable<Formula, List<VeritProofNode>>();
        for (VeritProofNode node : proof.getProofNodes()) {
            for (Formula litConclusion : node.getLiteralConclusions()) {
                Set<Integer> partitions = litConclusion
                        .getPartitionsFromSymbols();
                partitions.remove(-1);
                if (partitions.size() > 1) {
                    if (areSubproofsAllowed || node.getSubProofs() == null) {
                        List<VeritProofNode> proofNodes = badLiterals
                                .get(litConclusion);
                        if (proofNodes == null) {
                            proofNodes = new ArrayList<VeritProofNode>();
                            badLiterals.put(litConclusion, proofNodes);
                        }
                        proofNodes.add(node);
                    }
                }
                if (!Util.isLiteral(litConclusion)) {
                    // throw new
                    // RuntimeException("litConclusion is no literal.");
                    // System.err.println("litConclusion is no literal:"+litConclusion);
                }
            }
        }
        return badLiterals;
    }

    /**
     * Searches and returns for BadLiterals, that look like Implications (see
     * example), where the badLiteral is only in the positive form (see
     * example).
     * 
     * @param areSubproofsAllowed
     *            controls if subProofs should be allowed or not
     * @param filter
     *            only that type of ProodNode is returned, if filter != null
     * @return
     */
    public Hashtable<VeritProofNode, AbstractMap.SimpleEntry<Formula, List<Formula>>> findImplicationDefinitionsWithBadLiteralsOnlyinPositiveForm(
            boolean areSubproofsAllowed, Token filter) {
        // example:
        // a ^ b ^ c => d is the same as:
        // !a v !b v !c v d (because of that, I call it implications)
        // so d may contain bad Literals, but a,b,c mustnot contains badLiterals

        Hashtable<VeritProofNode, AbstractMap.SimpleEntry<Formula, List<Formula>>> implies = new Hashtable<VeritProofNode, AbstractMap.SimpleEntry<Formula, List<Formula>>>();
        Set<Integer> partitions;

        // Iterate through all proofNodes:
        for (VeritProofNode node : proof.getProofNodes()) {

            // If a filter is active, perform the filter:
            if (filter != null && !node.getType().equals(filter))
                continue;

            // if Subproofs are not allowed, filter out those with subProofs:
            if (!areSubproofsAllowed && node.getSubProofs() != null
                    && node.getSubProofs().size() > 0)
                continue;

            // check if this is an implication (TRANSITIVE or CONGRUENCE)
            // negated terms mustnot contain badLiterals
            // normal terms must contain a badLiteral (else we have nothing to
            // do)
            boolean ok = true;
            List<Formula> goodLiterals = new ArrayList<Formula>();
            List<Formula> badLiterals = new ArrayList<Formula>();

            // check if good literals are good:
            for (Formula litConclusion : node.getLiteralConclusions()) {
                partitions = litConclusion.getPartitionsFromSymbols();
                partitions.remove(-1);
                boolean contains_badliterals = partitions.size() > 1;

                // negated terms mustnot contain badLiterals
                if (litConclusion instanceof NotFormula
                        && !contains_badliterals) {
                    goodLiterals.add(litConclusion);
                }
                // normal terms must contain a badLiteral
                else if (!(litConclusion instanceof NotFormula)
                        && contains_badliterals) {
                    badLiterals.add(litConclusion);
                }
                // we cannot do anything about that until now
                else if (contains_badliterals) {
                    // System.err.println(node.toString());
                    ok = false;
                    break;
                }
                // we have no bad literals
                else {
                    ok = false;
                    break;
                }
            }

            // if we have an implication, exactly one can contain badLiterals
            if (ok && badLiterals.size() != 1)
                ok = false;
            // at least one mustnot be a badliteral
            if (ok && goodLiterals.size() < 1)
                ok = false;
            if (ok) {
                // the implication could already exists
                // I think they are sometimes multiple defined.
                // we could then also delete the node we found right now
                // and relink the parents to the given one
                // but then we should additionally check for the other
                // parameters

                implies.put(node,
                        new AbstractMap.SimpleEntry<Formula, List<Formula>>(
                                badLiterals.get(0), goodLiterals));

            }
        }
        return implies;
    }

    /**
     * Returns all unique badLiterals (Formulas) if any occurs in a Formula.
     * This may result in duplicate entries in the List for one VeriTProofNode.
     * 
     * @param areSubproofsAllowed
     *            if false, only nodes with no SubProofs are counted
     * @return a HashSet of unique Formulas that contains badLiterals
     */
    public Set<Formula> findBadLiterals(boolean areSubproofsAllowed) {
        // should be equal to:
        // findBadLiteralsWithProofNode(areSubproofsAllowed).keySet();

        Set<Formula> badLiterals = new HashSet<Formula>();
        for (VeritProofNode node : proof.getProofNodes()) {
            for (Formula litConclusion : node.getLiteralConclusions()) {
                Set<Integer> partitions = litConclusion
                        .getPartitionsFromSymbols();
                partitions.remove(-1);
                if (partitions.size() > 1) {
                    if (areSubproofsAllowed || node.getSubProofs() == null) {
                        badLiterals.add(litConclusion);
                    }
                }
            }
        }
        return badLiterals;
    }

    /**
     * Analyzes the badLiterals and writes the badLiterals in three files (see
     * parameters). Also counts some statistics and prints them to console.
     * 
     * @param erroraLiteralFile
     *            contains all Formulas that contains badLiterals, also
     *            duplicate.
     * @param errorClauselFile
     *            all VeriTNodes that contains badLiterals
     * @param errorNoChildren
     *            only writes nodes, that have no children.
     */
    public void analyzePartitions(File erroraLiteralFile,
            File errorClauselFile, File errorNoChildren) {
        System.out
                .println("* writing assert partition (literal) errors after veriT to '"
                        + erroraLiteralFile + "'");
        System.out
                .println("* writing assert partition (clauses) errors after veriT to '"
                        + errorClauselFile + "'");
        System.out
                .println("* writing assert partition (noChildren) errors after veriT to '"
                        + errorNoChildren + "'");

        FileWriter fstream = null;
        FileWriter fstream_more = null;
        FileWriter fstream_nochildren = null;
        try {
            fstream = new FileWriter(erroraLiteralFile);
            fstream_more = new FileWriter(errorClauselFile);
            fstream_nochildren = new FileWriter(errorNoChildren);

            int formulas = 0;
            int errors = 0;
            int errors_unique = 0;
            int errors_no_childs = 0;
            for (VeritProofNode node : proof.getProofNodes()) {
                int i = 0;
                boolean first_error = false;
                for (Formula litConclusion : node.getLiteralConclusions()) {
                    formulas++;
                    i++;
                    Set<Integer> partitions = litConclusion
                            .getPartitionsFromSymbols();
                    partitions.remove(-1);
                    if (partitions.size() > 1) {
                        errors++;
                        fstream.write("--------------------------------------------------\n");
                        fstream.write("Formula '" + node.getName() + "' #" + i
                                + " part:" + partitions + "\n");
                        fstream.write(litConclusion.toString());
                        fstream.write("\n");

                        if (!first_error) {
                            first_error = true;
                            errors_unique++;
                            fstream_more
                                    .write("\n\n--------------------------------------------------");
                            fstream_more.write("\nFormula '" + node.getName()
                                    + //
                                    "' of type '" + node.getType()
                                    + "'. Conclusion (in OR-Format):\n");
                            fstream_more
                                    .write(node.getConclusionsAsOrFormula().toString());

                            if (node.getSubProofs() == null) {
                                errors_no_childs++;
                                fstream_nochildren
                                        .write("\n\n--------------------------------------------------\n");
                                fstream_nochildren.write(node.toString());
                            }
                        }

                        // System.out.println("Formula '"+node.getName() +
                        // "' #"+i+" p:"+partitions);
                    }
                }
            }

            // Statistics:
            System.out.println("* There are " + errors + " errors in "
                    + errors_unique + " clauses of " + formulas + " formulas ("
                    + errors_no_childs + " errors without childs).");
        } catch (Exception ex) {
            ex.printStackTrace();
        } finally {
            try {
                if (fstream != null)
                    fstream.close();
                if (fstream_more != null)
                    fstream_more.close();
                if (fstream_nochildren != null)
                    fstream_nochildren.close();
            } catch (Exception ex) {
                ex.printStackTrace();
                throw new RuntimeException(ex);
            }
        }

    }

}
