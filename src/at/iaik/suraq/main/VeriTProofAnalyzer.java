package at.iaik.suraq.main;

import java.io.File;
import java.io.FileWriter;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.proof.VeritProof;
import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.util.Util;

public class VeriTProofAnalyzer {
    private final VeritProof proof;
    public VeriTProofAnalyzer(VeritProof proof)
    {
        this.proof = proof;
    }

    public void removeBadLiterals() {

        // in the first step, we only look for eq_transitive and eq_congruent,
        // which only occurs as leafs (no subProofs)
        // Set<Formula> badLiterals = this.findBadLiterals(false);
        // Hashtable<Formula, List<VeritProofNode>> badLiterals =
        // findBadLiteralsWithProofNode(false);
        Hashtable<Formula, AbstractMap.SimpleEntry<VeritProofNode, List<Formula>>> implications = findImplicationDefinitionsWithBadLiteralsOnlyinPositiveForm(false);
        System.out.println("Found "+implications.size()+" bad literals with no subProofs that only had bad literals in the positive form.");
        
        for (Formula badLiteral : implications.keySet()) {
            VeritProofNode start_node = implications.get(badLiteral).getKey();
            // these nodes have no childs
            List<Formula> conditions = implications.get(badLiteral).getValue();

            // 1. propagate to the parents till the (positive) badLiteral vanishes
            List<VeritProofNode> ends = new ArrayList<VeritProofNode>();
            replaceBadLiteralToParents(start_node, conditions, badLiteral, ends);


            // 2. propagate to the childs till the (negative) badLiteral vanishes
            // TODO: split the result in several steps
            NotFormula negatedBadLiteral = NotFormula.create(badLiteral);
            for (VeritProofNode end : ends) {
                replaceBadLiteralToSubProofs(end, conditions, negatedBadLiteral);
            }
            
            // 3. delete current node from proof
            proof.removeProofSet(start_node);

            // FIXME: stopped here 2012-08-09, 2012-08-10
        }
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
     * Propagate to the childs
     * 
     * @param node
     * @param conditions conditions in negated form
     * @param badLiteral badLiteral in negated form
     */
    private void replaceBadLiteralToSubProofs(VeritProofNode node,
            List<Formula> conditions, Formula badLiteral) {
        if(node.getSubProofs() == null)
            return;
        for (VeritProofNode child : node.getSubProofs()) {
            List<Formula> formulas = child.getLiteralConclusions(); // no copy!
            int index = formulas.indexOf(badLiteral);
            if(index == -1)
            {
                // the badLiteral does not occur any more :-)
            }
            else
            {
                System.out.print('-');
                formulas.addAll(conditions);
                replaceBadLiteralToSubProofs(child, conditions, badLiteral);
            }
        }
    }
    
    /**
     * Propagate to the Parents
     * @param node
     * @param conditions
     * @param badLiteral
     * @param ends
     */
    private void replaceBadLiteralToParents(VeritProofNode node, List<Formula> conditions, Formula badLiteral, List<VeritProofNode> ends)
    {
        // badLiteral is in Positive Form, conditions are in Negated Form
        if(node.getParents() == null)
            return;
        for(VeritProofNode parent : node.getParents())
        {
            List<Formula> formulas = parent.getLiteralConclusions(); // no copy!
            int position = formulas.indexOf(badLiteral);
            if(position != -1)
            {
                System.out.print('+');
                //formulas.remove(position);
                formulas.set(position, AndFormula.generate(removeNotFormulas(conditions)));
                replaceBadLiteralToParents(parent, conditions, badLiteral, ends);
            }
            else
            {
                // we have reached the end of the downpropagation
                ends.add(parent);
            }
        }
    }
    
    public void analyzeBadLiteralsSat(File fileBadLiterals)
    {
        
        Set<Formula> badLiterals = findBadLiterals(false);
        System.out.println("There were "+ badLiterals.size()+" bad literals.");
        badLiterals = satisfyBadLiterals(badLiterals);
        System.out.println("There were "+ badLiterals.size()+" bad literals after satisfying positive-negative ones.");
        
        int literals = 0;
        int noliterals = 0;
        for(Formula badLiteral : badLiterals)
        {
            if(Util.isLiteral(badLiteral))
                literals++;
            else
                noliterals++;
        }
        System.out.println("These bad literals were "+ literals+" literals and "+noliterals+" not literals.");
        
        try
        {
            FileWriter fstream = new FileWriter(fileBadLiterals);
            for(Formula badLiteral : badLiterals)
            {
                fstream.write("\n--------------------------------\n");
                fstream.write(badLiteral.toString());
            }
            fstream.close();
        }
        catch(Exception ex)
        {
            
        }
    }
    
    
    
    private boolean isDebugStop(Formula formula, String varname1, String varname2)
    {
        Set<Token> tokens = new HashSet<Token>();
        tokens.add(Token.generate(varname2));
        if(Util.formulaContainsAny(formula, tokens))
        {
            tokens.clear();
            tokens.add(Token.generate(varname1));

            if(Util.formulaContainsAny(formula, tokens))
            {
                return true;
            }
        }
        return false;
        
    }
    
    public Set<Formula> satisfyBadLiterals(Set<Formula> badLiterals)
    {
        Set<Formula> filteredBadLiterals = new HashSet<Formula>();
        int positiveElements = 0;
        Set<Formula> veryBadLiterals = new HashSet<Formula>();
        for(Formula badLiteral : badLiterals)
        {
            if(badLiteral instanceof NotFormula)
            {
                filteredBadLiterals.add(Util.makeLiteralPositive(badLiteral));
            }
            else if(!Util.isLiteral(badLiteral))
            {
                // TODO: very bad "literals"!!!
                if(badLiteral instanceof NotFormula)
                {
                    filteredBadLiterals.add(((NotFormula)badLiteral).getNegatedFormula());
                }
                else
                    veryBadLiterals.add(badLiteral);
            }
            else
                positiveElements++;
            // else: that's ok
        }
        System.out.println("removed "+positiveElements+" elements because they were positive");
        
        // filteredBadLiterals are positive now
        int removed_elements = 0;
        int not_removed_elements = 0;
        for(Formula badLiteral : badLiterals)
        {
            if(isDebugStop(badLiteral,"marci3__copy_1","marci3__copy_4"))
            {
                System.out.print("");
            }
            if(filteredBadLiterals.remove(badLiteral))
                removed_elements++;
            else if(!(badLiteral instanceof NotFormula))
                not_removed_elements++;
        }
        System.out.println("removed "+removed_elements+" elements on filtering and "+not_removed_elements+" were not to remove.");
        
        System.out.println("There were "+ veryBadLiterals.size() +" Literals, that were no literals and no NOT-formula");
        filteredBadLiterals.addAll(veryBadLiterals);
        return filteredBadLiterals;
    }
    
    /**
     * Finds bad literals and stores to each one, in which nodes it occured
     * @param areSubproofsAllowed defines if found elements may contain subproofs
     * @return
     */
    public Hashtable<Formula, List<VeritProofNode>> findBadLiteralsWithProofNode(boolean areSubproofsAllowed)
    {
        Hashtable<Formula, List<VeritProofNode>> badLiterals = new Hashtable<Formula, List<VeritProofNode>>();
        for (VeritProofNode node : proof.getProofNodes()) {
            for (Formula litConclusion : node.getLiteralConclusions()) {
                Set<Integer> partitions = litConclusion
                        .getPartitionsFromSymbols();
                partitions.remove(-1);
                if (partitions.size() > 1) {
                    if (areSubproofsAllowed || node.getSubProofs() == null) {
                        List<VeritProofNode> proofNodes = badLiterals.get(litConclusion);
                        if(proofNodes == null)
                        {
                            proofNodes = new ArrayList<VeritProofNode>();
                            badLiterals.put(litConclusion, proofNodes);
                        }
                        proofNodes.add(node);
                    }
                }
                if(!Util.isLiteral(litConclusion))
                {
                    //throw new RuntimeException("litConclusion is no literal.");
                    //System.err.println("litConclusion is no literal:"+litConclusion);
                }
            }
        }
        return badLiterals;
    }
    
    public Hashtable<Formula, AbstractMap.SimpleEntry<VeritProofNode, List<Formula>>> findImplicationDefinitionsWithBadLiteralsOnlyinPositiveForm(
            boolean areSubproofsAllowed) {
        Hashtable<Formula, AbstractMap.SimpleEntry<VeritProofNode, List<Formula>>> implies = new Hashtable<Formula, AbstractMap.SimpleEntry<VeritProofNode, List<Formula>>>();
        Set<Integer> partitions;
        for (VeritProofNode node : proof.getProofNodes()) {
            if (!areSubproofsAllowed && node.getSubProofs() != null)
                continue;

            boolean ok = true;
            List<Formula> goodLiterals = new ArrayList<Formula>(
                    node.getLiteralConclusions());
            Formula badLiteral = goodLiterals.get(goodLiterals.size() - 1);

            if (badLiteral instanceof NotFormula) {
                continue;
            }

            // check if good literals are good:
            for (Formula litConclusion : goodLiterals) {
                if (litConclusion instanceof NotFormula) {
                    ok = false;
                    break;
                }
                partitions = litConclusion.getPartitionsFromSymbols();
                partitions.remove(-1);
                if (partitions.size() > 1) {
                    ok = false;
                    break;
                }
            }

            // check if bad literal is bad:
            partitions = badLiteral.getPartitionsFromSymbols();
            partitions.remove(-1);
            if (partitions.size() > 1) {
                ok = false;
            }

            if (ok) {
                implies.put(
                        badLiteral,
                        new AbstractMap.SimpleEntry<VeritProofNode, List<Formula>>(
                                node, goodLiterals));
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
                if(!Util.isLiteral(litConclusion))
                {
                    //throw new RuntimeException("litConclusion is no literal.");
                    //System.err.println("litConclusion is no literal:"+litConclusion);
                }
            }
        }
        return badLiterals;
    }

    /**
     * To analyze the Partitions of the Formula, the Partition-flag in the FOrmulas must be correct!
     * @param assertPartitionFormulas
     */
    public void analyzePartitions(
            Map<Integer, Formula> assertPartitionFormulas, File erroraLiteralFile, File errorClauselFile, File errorNoChildren) {
        System.out.println("* writing assert partition (literal) errors after veriT to '"
                + erroraLiteralFile + "'");
        System.out.println("* writing assert partition (clauses) errors after veriT to '"
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
                            fstream_more.write(node.getConclusions().toString());
                            
                            if(node.getSubProofs() == null )
                            {
                                errors_no_childs ++;
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
                if(fstream_nochildren != null)
                    fstream_nochildren.close();
            } catch (Exception ex) {

            }
        }

    }
    
}
