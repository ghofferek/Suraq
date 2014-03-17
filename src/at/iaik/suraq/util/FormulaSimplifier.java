/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;

/**
 * 
 * Simplifies formulas using external tools (abc).
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class FormulaSimplifier {

    public static final String SIMPLIFIER_PATH = "./lib/simplifier/simplify.sh";

    private static final long CHECK_TRESHOLD = 10000;

    /**
     * The originalFormula, unsimplified formula.
     */
    private final Formula originalFormula;

    /**
     * The simplified formula, or <code>null</code> if simplification was not
     * successfully performed (yet).
     */
    private Formula simplifiedFormula;

    /**
     * The encoding of literals.
     */
    private Map<Formula, Integer> literalEncoding = new HashMap<Formula, Integer>();

    public FormulaSimplifier(Formula original) {
        assert (original != null);
        this.originalFormula = original;
    }

    /**
     * Simplifies the formula.
     * 
     * @throws IOException
     * 
     */
    public void simplify() throws IOException {
        Util.printToSystemOutWithWallClockTimePrefix("Simplifying a formula with abc.");
        File originalFile = File.createTempFile("originalFormula", ".aag",
                new File("./"));
        File resultFile = File.createTempFile("simplifiedFormula", ".aag",
                new File("./"));
        Util.printToSystemOutWithWallClockTimePrefix("Temporary aiger file for original formula: "
                + originalFile.toString());
        writeToFile(originalFile);
        Util.printToSystemOutWithWallClockTimePrefix("Starting abc.");
        ProcessResult result = ProcessUtil
                .runExternalProcess(
                        FormulaSimplifier.SIMPLIFIER_PATH + " "
                                + originalFile.toString() + " "
                                + resultFile.toString(), "");
        if (result.getExitCode() != 0)
            throw new RuntimeException("Error during abc simplification");
        Util.printToSystemOutWithWallClockTimePrefix("Parsing abc results from aiger file "
                + resultFile.toString());
        simplifiedFormula = parseResult(resultFile);
        Util.printToSystemOutWithWallClockTimePrefix("Done with simplification");

    }

    /**
     * @param originalFile
     * @throws IOException
     */
    private void writeToFile(File originalFile) throws IOException {
        Set<Formula> literals = new HashSet<Formula>();
        Set<Formula> done = new HashSet<Formula>();
        originalFormula.getLiterals(literals, done);

        TreeMap<Integer, Integer[]> aigNodes = new TreeMap<Integer, Integer[]>();

        int count = 2;
        for (Formula literal : literals) {
            literalEncoding.put(literal, count);
            count += 2;
        }
        Map<Formula, Integer> aigEncoding = new HashMap<Formula, Integer>(
                literalEncoding);
        originalFormula.toAig(aigNodes, aigEncoding);

        FileWriter fwriter = new FileWriter(originalFile);
        BufferedWriter writer = new BufferedWriter(fwriter);

        writer.write("aag ");
        writer.write(Integer.toString(aigNodes.descendingKeySet().iterator()
                .next() / 2)); // Max variable index
        writer.write(" ");
        writer.write(Integer.toString(literals.size())); // Num inputs
        writer.write(" 0 1 "); // Num latches & num outputs
        writer.write(Integer.toString(aigNodes.size())); // Num AND gates
        writer.write("\n");

        // Inputs
        for (Formula literal : literals) {
            Integer aigVariable = aigEncoding.get(literal);
            writer.write(aigVariable.toString());
            writer.write("\n");
        }

        // Output
        writer.write(aigEncoding.get(originalFormula).toString());
        writer.write("\n");

        // AND gates
        for (Integer gate : aigNodes.keySet()) {
            writer.write(gate.toString());
            writer.write(" ");
            Integer[] rhs = aigNodes.get(gate);
            assert (rhs.length == 2);
            writer.write(rhs[0].toString());
            writer.write(" ");
            writer.write(rhs[1].toString());
            writer.write("\n");
        }

        // Symbol table
        count = 0;
        for (Formula literal : literals) {
            writer.write("i");
            writer.write(Integer.toString(count));
            writer.write(" ");
            writer.write(literal.toString().replaceAll("\\s{2,}", " ")
                    .replace("\n", ""));
            writer.write("\n");
            count++;
        }

        writer.close();
        fwriter.close();
    }

    /**
     * Parses the result of simplification from the given file.
     * 
     * @param resultFile
     * @throws IOException
     */
    private Formula parseResult(File resultFile) throws IOException {
        FileReader freader = new FileReader(resultFile);
        BufferedReader reader = new BufferedReader(freader);

        String[] firstLine = reader.readLine().split(" ");
        assert (firstLine.length == 6);
        assert (firstLine[0].equals("aag"));

        int maxVarIndex = Integer.parseInt(firstLine[1]);
        int numInputs = Integer.parseInt(firstLine[2]);
        int numLatches = Integer.parseInt(firstLine[3]);
        int numOutputs = Integer.parseInt(firstLine[4]);
        int numAndGates = Integer.parseInt(firstLine[5]);

        assert (numLatches == 0);
        assert (numOutputs == 1);
        assert (numInputs == literalEncoding.size());
        assert (maxVarIndex >= numInputs + numLatches + numAndGates);

        // Skip lines defining inputs
        for (int count = 0; count < numInputs; count++)
            reader.readLine();

        String outputLine = reader.readLine();
        int outputLiteral = Integer.parseInt(outputLine);

        Map<Integer, Integer[]> andGates = new TreeMap<Integer, Integer[]>();
        for (int count = 0; count < numAndGates; count++) {
            String line = reader.readLine();
            String[] gateDef = line.split(" ");
            assert (gateDef.length == 3);
            Integer[] rhs = { Integer.parseInt(gateDef[1]),
                    Integer.parseInt(gateDef[2]) };
            andGates.put(Integer.parseInt(gateDef[0]), rhs);
        }
        reader.close();
        freader.close();

        Map<Integer, Formula> done = new HashMap<Integer, Formula>();
        for (Formula literal : literalEncoding.keySet()) {
            Integer aigLit = literalEncoding.get(literal);
            done.put(aigLit, literal);
        }
        return aigToFormula(outputLiteral, andGates, done);
    }

    /**
     * Returns the formula corresponding the the given <code>aigLit</code>.
     * 
     * @param aigLit
     * @param andGates
     * @param done
     * @return
     */
    private Formula aigToFormula(int aigLit, Map<Integer, Integer[]> andGates,
            Map<Integer, Formula> done) {
        if (done.get(aigLit) != null)
            return done.get(aigLit);

        if (aigLit == 0)
            return PropositionalConstant.create(false);
        if (aigLit == 1)
            return PropositionalConstant.create(true);

        boolean negated = aigLit % 2 == 1;
        int posAigLit = aigLit & 0xFFFFFFFE;
        if (done.get(posAigLit) != null) {
            assert (negated);
            Formula result = NotFormula.create(done.get(posAigLit));
            done.put(aigLit, result);
            return result;
        }

        Integer[] gate = andGates.get(posAigLit);
        assert (gate.length == 2);
        Formula firstConjunct = aigToFormula(gate[0], andGates, done);
        Formula secondConjunct = aigToFormula(gate[1], andGates, done);
        List<Formula> conjuncts = new ArrayList<Formula>(2);
        conjuncts.add(firstConjunct);
        conjuncts.add(secondConjunct);
        Formula andFormula = AndFormula.generate(conjuncts);

        Formula result = negated ? NotFormula.create(andFormula) : andFormula;
        done.put(aigLit, result);
        return result;
    }

    /**
     * @return the <code>simplifiedFormula</code>
     */
    public Formula getSimplifiedFormula() {
        return simplifiedFormula;
    }

    /**
     * @return the <code>originalFormula</code>
     */
    public Formula getOriginalFormula() {
        return originalFormula;
    }

    /**
     * Performs check of equivalence between original and simplified formula.
     * This might be infeasible for large (original) formulas.
     * 
     * @return <code>true</code> iff the original formula is equivalent to the
     *         simplified formula.
     */
    public boolean checkSimplification() {
        // try {
        // assert (checkWriteReadOriginalFormula());
        // } catch (IOException exc) {
        // exc.printStackTrace();
        // throw new RuntimeException(exc);
        // }
        long size = originalFormula.size(true, new HashMap<Formula, Long>());
        if (size > FormulaSimplifier.CHECK_TRESHOLD) {
            Util.printToSystemOutWithWallClockTimePrefix("WARNING: Skipped check of simplification because original formula has tree-size "
                    + Util.largeNumberFormatter.format(size));
            return true;
        }

        return Util.checkEquivalenceOfFormulas(originalFormula,
                simplifiedFormula);
    }

    /**
     * Writes the original formula to an AIGER file and reads it back in. This
     * method servers purely testing purposes and has no practical significance.
     * (That's why it is marked Deprecated.)
     * 
     * @return <code>true</code> iff the formula that was read back in equals
     *         the original formula.
     * @throws IOException
     */
    @Deprecated
    public boolean checkWriteReadOriginalFormula() throws IOException {
        File testFile = File.createTempFile("testAigWriteRead", ".aag",
                new File("./"));

        writeToFile(testFile);
        Formula testFormula = parseResult(testFile);
        return Util.checkEquivalenceOfFormulas(originalFormula, testFormula);
    }
}
