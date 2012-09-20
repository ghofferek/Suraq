package at.iaik.suraq.main;

import java.io.File;
import java.io.FileWriter;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.proof.VeriTToken;
import at.iaik.suraq.proof.VeritProof;
import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.util.Util;

public class VeriTProofAnalyzer {
    private final VeritProof proof;

    public VeriTProofAnalyzer(VeritProof proof) {
        this.proof = proof;
    }

    public void removeBadLiterals() {
        {
            System.out.println(">> removeBadLiterals (TRANS): proof-size: "
                    + proof.getProofNodes().size() + " literals:"
                    + proof.getLiteralConclusionsCount() + " bad: "
                    + this.findBadLiterals(true).size() + " <<");
            while (removeBadLiteralsTransitive(VeriTToken.EQ_TRANSITIVE)) {
                System.out.println(">> removeBadLiterals (TRANS): proof-size: "
                        + proof.getProofNodes().size() + " literals:"
                        + proof.getLiteralConclusionsCount() + " bad: "
                        + this.findBadLiterals(true).size() + " <<");
            }
        }

        {
            System.out.println(">> removeBadLiterals (CONGR): proof-size: "
                    + proof.getProofNodes().size() + " literals:"
                    + proof.getLiteralConclusionsCount() + " bad: "
                    + this.findBadLiterals(true).size() + " <<");
            while (removeBadLiteralsTransitive(VeriTToken.EQ_CONGRUENT)) {
                System.out.println(">> removeBadLiterals (CONGR): proof-size: "
                        + proof.getProofNodes().size() + " literals:"
                        + proof.getLiteralConclusionsCount() + " bad: "
                        + this.findBadLiterals(true).size() + " <<");
            }
        }
    }

    private boolean removeBadLiteralsTransitive(Token type) {

        // in the first step, we only look for eq_transitive and eq_congruent,
        // which only occurs as leafs (no subProofs)
        // Set<Formula> badLiterals = this.findBadLiterals(false);
        // Hashtable<Formula, List<VeritProofNode>> badLiterals =
        // findBadLiteralsWithProofNode(false);
        Hashtable<VeritProofNode, AbstractMap.SimpleEntry<Formula, List<Formula>>> implications = findImplicationDefinitionsWithBadLiteralsOnlyinPositiveForm(
                false, type);
        System.out
                .println("\n Found "
                        + implications.size()
                        + " bad literals with no subProofs that only had bad literals in the positive form.");

        for (VeritProofNode start_node : implications.keySet()) {
            Formula badLiteral = implications.get(start_node).getKey();
            // these nodes have no children
            List<Formula> conditions = implications.get(start_node).getValue();

            if (start_node.getSubProofs() != null) {
                continue;
            }

            // System.out.print(start_node.getName()+"("+start_node.getType()+"): ");

            // 1. propagate to the parents till the (positive) badLiteral
            // vanishes
            List<VeritProofNode> ends = new ArrayList<VeritProofNode>();
            replaceBadLiteralToParents(start_node, conditions, badLiteral, ends);

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

            // FIXME: stopped here 2012-08-09, 2012-08-10
            // System.out.print('\n');
        }
        return implications.size() > 0;
    }

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
     * Propagate to the children
     * 
     * @param node
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
            if (child.getType().equals(VeriTToken.EQ_TRANSITIVE)) {
                System.out.print(""); // DEBUG point
            }
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

    public void analyzeBadLiteralsSat(File fileBadLiterals) {

        Set<Formula> badLiterals = findBadLiterals(false);
        System.out.println("\nThere were " + badLiterals.size()
                + " unique bad literals. Hash: " + badLiterals.hashCode());
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

    private boolean isDebugStop(Formula formula, String varname1,
            String varname2) {
        Set<Token> tokens = new HashSet<Token>();
        tokens.add(Token.generate(varname2));
        if (Util.formulaContainsAny(formula, tokens)) {
            tokens.clear();
            tokens.add(Token.generate(varname1));

            if (Util.formulaContainsAny(formula, tokens)) {
                return true;
            }
        }
        return false;

    }

    public Set<Formula> satisfyBadLiterals(Set<Formula> badLiterals) {
        Set<Formula> filteredBadLiterals = new HashSet<Formula>();
        int positiveElements = 0;
        Set<Formula> veryBadLiterals = new HashSet<Formula>();
        for (Formula badLiteral : badLiterals) {
            if (badLiteral instanceof NotFormula) {
                filteredBadLiterals.add(Util.makeLiteralPositive(badLiteral));
            } else if (!Util.isLiteral(badLiteral)) {
                // TODO: very bad "literals"!!!
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
            if (isDebugStop(badLiteral, "marci3__copy_1", "marci3__copy_4")) {
                System.out.print("");
            }
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

    public Hashtable<VeritProofNode, AbstractMap.SimpleEntry<Formula, List<Formula>>> findImplicationDefinitionsWithBadLiteralsOnlyinPositiveForm(
            boolean areSubproofsAllowed, Token filter) {
        Hashtable<VeritProofNode, AbstractMap.SimpleEntry<Formula, List<Formula>>> implies = new Hashtable<VeritProofNode, AbstractMap.SimpleEntry<Formula, List<Formula>>>();
        Set<Integer> partitions;
        for (VeritProofNode node : proof.getProofNodes()) {
            if (filter != null && !node.getType().equals(filter))
                continue;
            if (!areSubproofsAllowed && node.getSubProofs() != null
                    && node.getSubProofs().size() > 0)
                continue;

            boolean ok = true;
            List<Formula> goodLiterals = new ArrayList<Formula>();
            List<Formula> badLiterals = new ArrayList<Formula>();

            if (node.getType().equals(VeriTToken.EQ_TRANSITIVE)) {
                System.out.print(""); // DEBUG POINT
            }

            // check if good literals are good:
            for (Formula litConclusion : node.getLiteralConclusions()) {
                partitions = litConclusion.getPartitionsFromSymbols();
                partitions.remove(-1);
                boolean contains_badliterals = partitions.size() > 1;

                if (litConclusion instanceof NotFormula
                        && !contains_badliterals) {
                    goodLiterals.add(litConclusion);
                } else if (!(litConclusion instanceof NotFormula)
                        && contains_badliterals) {
                    badLiterals.add(litConclusion);
                } else if (contains_badliterals) {
                    // System.err.println(node.toString());
                    ok = false;
                    break;
                } else {
                    ok = false;
                    break;
                }
            }

            if (ok && badLiterals.size() != 1)
                ok = false;
            if (ok && goodLiterals.size() < 1)
                ok = false;
            if (ok) {
                // the implication could already exists
                // we could also delete the node we found right now
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
     * To analyze the Partitions of the Formula, the Partition-flag in the
     * FOrmulas must be correct!
     * 
     * @param assertPartitionFormulas
     */
    public void analyzePartitions(File erroraLiteralFile,
            File errorClauselFile, File errorNoChildren) {
        System.out
                .println("* writing assert partition (literal) errors after veriT to '"
                        + erroraLiteralFile + "'");
        System.out
                .println("* writing assert partition (clauses) errors after veriT to '"
                        + errorClauselFile + "'");
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
                                    + "'. Conclusion (OR):\n");
                            fstream_more
                                    .write(node.getConclusions().toString());

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
            System.out.println("* There are " + errors + " errors in "
                    + errors_unique + " clauses of " + formulas + " formulas("
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

            }
        }

    }

}
