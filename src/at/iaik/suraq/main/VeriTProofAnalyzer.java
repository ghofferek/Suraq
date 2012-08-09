package at.iaik.suraq.main;

import java.io.File;
import java.io.FileWriter;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.proof.VeritProof;
import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.util.Util;

public class VeriTProofAnalyzer {
    private final VeritProof proof;
    public VeriTProofAnalyzer(VeritProof proof)
    {
        this.proof = proof;
    }
    
    
    public void removeBadLiterals()
    {
        // true = subproofs are allowed
        Set<Formula> badLiterals = this.findBadLiterals(true);
        // we must know to which Proof the bad literals belong.
        // therefore we must change the findBadLiteralsSearch.
        
        
        // FIXME: stopped here 2012-08-09 
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
                System.out.println("");
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
    
    public Set<Formula> findBadLiterals(boolean areSubproofsAllowed) {
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
