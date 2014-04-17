/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.main;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.math.BigInteger;
import java.text.DecimalFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.parser.FormulaParser;
import at.iaik.suraq.parser.LogicParser;
import at.iaik.suraq.parser.ProofParser;
import at.iaik.suraq.parser.SExpParser;
import at.iaik.suraq.parser.TseitinParser;
import at.iaik.suraq.parser.VeriTParser;
import at.iaik.suraq.proof.VeritProof;
import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.resProof.ResNode;
import at.iaik.suraq.resProof.ResProof;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.smtlib.TransformedZ3Proof;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.FormulaTerm;
import at.iaik.suraq.smtlib.formula.FunctionMacro;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.smtlib.formula.PropositionalTerm;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtsolver.SMTSolver;
import at.iaik.suraq.smtsolver.VeriTSolver;
import at.iaik.suraq.smtsolver.z3;
import at.iaik.suraq.util.BenchmarkTimer;
import at.iaik.suraq.util.DebugHelper;
import at.iaik.suraq.util.FormulaSimplifier;
import at.iaik.suraq.util.Timer;
import at.iaik.suraq.util.Util;

/**
 * 
 * This is the main class of the Suraq project. Control flow will start here.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class Suraq implements Runnable {
    public static final BenchmarkTimer extTimer = new BenchmarkTimer();

    /**
     * Timer for overall execution
     */
    private Timer overallTimer = new Timer();

    /**
     * The parser that holds the data of the main formula from which to
     * synthesize.
     */
    private LogicParser logicParser;

    /**
     * The special variable that is used for reducing array properties to finite
     * conjunctions.
     */
    private DomainVariable lambda;

    // /**
    // * The expressions that will be written to the output.
    // */
    // private List<SExpression> outputExpressions;

    /**
     * Maps each noDependenceVar to a list of its copies.
     */
    private Map<Token, List<Term>> noDependenceVarsCopies;

    /**
     * Maps each noDependenceFunction to a list of its copies.
     */
    private Map<Token, List<UninterpretedFunction>> noDependenceFunctionsCopies;

    /**
     * Mapping variable names to their type.
     */
    private Map<Token, SExpression> varTypes;

    /**
     * Stores whether or not any (serious) errors occurred.
     */
    private boolean noErrors = true;

    /**
     * stores the declaration part of the smt description
     */
    private String declarationStr = "";

    /**
     * Stores the encoding from Tseitin variables to their formulas.
     */
    private Map<PropositionalVariable, Formula> tseitinEncoding = new HashMap<PropositionalVariable, Formula>();

    /**
     * stores the assert partitions of the smt description
     */
    // TODO: REMOVE, use assertPartitionFormulas
    @Deprecated
    private List<SExpression> assertPartitionList = new ArrayList<SExpression>();
    /**
     * stores the main formula
     */
    private Formula mainFormula = null;

    /**
     * stores all present propositional variables
     */
    private Set<PropositionalVariable> propositionalVars = new HashSet<PropositionalVariable>();
    /**
     * stores all present domain variables
     */
    private Set<DomainVariable> domainVars = new HashSet<DomainVariable>();
    /**
     * stores all present array variables
     */
    private Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();
    /**
     * stores all present uninterpreted functions
     */
    private Set<UninterpretedFunction> uninterpretedFunctions = new HashSet<UninterpretedFunction>();

    /**
     * Constraints for variables newly introduced during reductions.
     */
    private Set<Formula> constraints = new HashSet<Formula>();

    /**
     * stores the assert partition formula for each assert partition
     */
    private TreeMap<Integer, Formula> assertPartitionFormulas = new TreeMap<Integer, Formula>();

    private VeritProof veritProof = null;

    private Set<Token> noDependenceVars;

    /**
     * Stores the Tseitin-encoded partitions.
     */
    private TreeMap<Integer, Formula> tseitinPartitions = new TreeMap<Integer, Formula>();

    /**
     * Constructs a new <code>Suraq</code>.
     */
    public Suraq(String[] args) {
        try {
            SuraqOptions.initialize(args);
        } catch (SuraqException exc) {
            System.err
                    .println("Error in parsing options. Unparseable options will be overriden by defaults. Details follow.");
            exc.printStackTrace();
        }
    }

    /**
     * Checks whether everything was successful.
     * 
     * @return <code>false</code> if there were errors, <code>true</code>
     *         otherwise.
     */
    public boolean success() {
        return noErrors;
    }

    /**
     * This is the main entry point into the program.
     * 
     * @param args
     *            command-line arguments
     */
    public static void main(String[] args) {

        try {
            Suraq.extTimer.start();
            Suraq.extTimer.stopReset("start");
            Suraq suraq = new Suraq(args);
            suraq.run();

        } catch (Throwable exc) {
            Util.printMemoryInformation();
            Util.printToSystemOutWithWallClockTimePrefix("Program ended with an Exception");
            System.err.println("ERROR: Uncaught exception!");
            System.err.println("Message:" + exc.getMessage() == null ? "<null>"
                    : exc.getMessage());
            exc.printStackTrace();
            System.exit(-1);
        }
        System.exit(0);
    }

    private void parseInput() {
        SuraqOptions options = SuraqOptions.getInstance();
        File sourceFile = new File(options.getInput());
        Util.printToSystemOutWithWallClockTimePrefix("Starting to read "
                + sourceFile.getPath() + " ...");

        SExpParser sExpParser = null;
        try {
            sExpParser = new SExpParser(sourceFile);
        } catch (FileNotFoundException exc) {
            System.err.println("ERROR: File " + sourceFile.getPath()
                    + " not found!");
            noErrors = false;
            throw new RuntimeException(exc);
        } catch (IOException exc) {
            System.err.println("ERROR: Could not read from file "
                    + sourceFile.getPath());
            noErrors = false;
            throw new RuntimeException(exc);
        }

        Timer sExpParseTimer = new Timer();
        sExpParseTimer.start();
        try {
            sExpParser.parse();
            assert (sExpParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            noErrors = false;
            throw new RuntimeException(exc);
        } finally {
            sExpParseTimer.stop();
            Util.printToSystemOutWithWallClockTimePrefix("S-Expression parsing took "
                    + sExpParseTimer);
        }

        logicParser = new LogicParser(sExpParser.getRootExpr());

        sExpParser = null; // Allow this to be garbage collected

        Timer logicParseTimer = new Timer();
        try {
            logicParseTimer.start();
            logicParser.parse();
            assert (logicParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            noErrors = false;
            throw new RuntimeException(exc);
        } finally {
            logicParseTimer.stop();
            Util.printToSystemOutWithWallClockTimePrefix("Logic parsing took "
                    + logicParseTimer);
        }
        // Parsing complete
        if (options.isVerbose())
            Util.printToSystemOutWithWallClockTimePrefix("Parsing completed successfully!");
    }

    /**
     * Input transformations as they are used in non-iterative mode
     * 
     * @param sourceFile
     * @return
     */
    private void inputTransformations(File sourceFile) {
        DebugHelper.getInstance().setFolder(sourceFile.getPath() + "_out/");
        SuraqOptions options = SuraqOptions.getInstance();

        Suraq.extTimer.stopReset("<inputTransformations>");
        parseInput();
        try {
            mainFormula = doMainWork();
        } catch (SuraqException exc) {
            noErrors = false;
            if (exc.getMessage() != null)
                System.err.println(exc.getMessage());
        }

        // build function and variable lists for parser

        if (mainFormula == null) {
            // abort (workaround not to crash for QBF-Enc)
            return;
        }

        Util.printToSystemOutWithWallClockTimePrefix("  build function and variable lists for parser");
        propositionalVars.clear();
        mainFormula.getPropositionalVariables(propositionalVars,
                new HashSet<SMTLibObject>());
        domainVars.clear();
        mainFormula.getDomainVariables(domainVars, new HashSet<SMTLibObject>());
        arrayVars.clear();
        mainFormula.getArrayVariables(arrayVars, new HashSet<SMTLibObject>());
        uninterpretedFunctions.clear();
        mainFormula.getUninterpretedFunctions(uninterpretedFunctions,
                new HashSet<SMTLibObject>());

        for (Map.Entry<Token, List<Term>> varList : noDependenceVarsCopies
                .entrySet()) {
            assert (varList.getValue() != null);
            assert (varList.getValue().size() > 0);

            Term first = varList.getValue().get(0);

            if (first instanceof DomainVariable)
                for (Term var : varList.getValue())
                    domainVars.add((DomainVariable) var);

            if (first instanceof PropositionalVariable)
                for (Term var : varList.getValue())
                    propositionalVars.add((PropositionalVariable) var);

            if (first instanceof ArrayVariable)
                for (Term var : varList.getValue())
                    arrayVars.add((ArrayVariable) var);
        }

        for (Map.Entry<Token, List<UninterpretedFunction>> functionList : noDependenceFunctionsCopies
                .entrySet())
            uninterpretedFunctions.addAll(functionList.getValue());

        // debug
        // try {
        // Util.printToSystemOutWithWallClockTimePrefix("  Saving Debugfile ./debug_nodepvar.txt");
        // File debugFile1 = new File("./debug_nodepvar.txt");
        // FileWriter fstream = new FileWriter(debugFile1);
        // fstream.write(mainFormula.toString());
        // fstream.close();
        // } catch (Exception ex) {
        // ex.printStackTrace();
        // }

        if (options.getDumpSMTQueryFile() != null) {
            dumpSMTQuery(options.getDumpSMTQueryFile());
        }

        Util.printToSystemOutWithWallClockTimePrefix("  Simplifying assert-partitions and tseitin-cnf encoding...");

        Timer allPartitionsTimer = new Timer();
        allPartitionsTimer.start();

        boolean activetseitin = true;
        if (activetseitin) {

            Suraq.extTimer.stopReset("before tseitin");
            if (options.getTseitinType() == SuraqOptions.TSEITIN_WITHOUT_Z3) {
                Util.printToSystemOutWithWallClockTimePrefix("  Performing tseitin encoding without Z3...");
                performTseitinEncodingWithoutZ3();
            } else {
                Util.printToSystemOutWithWallClockTimePrefix("  Performing tseitin encoding with Z3...");
                performTseitinEncodingWithZ3();
            }
            Suraq.extTimer.stopReset("after tseitin");
            // DebugHelper.getInstance().stringtoFile(tseitinPartitions.toString(),
            // "tseitin-all.txt");

            allPartitionsTimer.end();
            Util.printToSystemOutWithWallClockTimePrefix("  All partitions done. ("
                    + allPartitionsTimer + ")");

            Suraq.extTimer
                    .stopReset("after buildSMTDescriptionFromTseitinPartitions");
        }
        Suraq.extTimer.stopReset("</inputTransformations>");
    }

    /**
     * Performs the tseitin encoding for each partition. Therefore it uses the
     * Z3 solver. Adds the encoding for each tseitin variable in the
     * <code>tseitinEncoding</code> map and returns the new encoded partitions.
     * 
     * @return the tseitin encoded partitions
     * 
     */
    @Deprecated
    private void performTseitinEncodingWithZ3() {

        int count = 1;
        Timer onePartitionTimer = new Timer();
        Timer timer2 = new Timer();
        z3 z3 = (at.iaik.suraq.smtsolver.z3) SMTSolver.create(
                SMTSolver.z3_type, SuraqOptions.getZ3_4Path());

        for (Integer partition : assertPartitionFormulas.keySet()) {
            Formula assertPartition = assertPartitionFormulas.get(partition);

            onePartitionTimer.reset();
            onePartitionTimer.start();

            Util.printToSystemOutWithWallClockTimePrefix("    Encoding partition "
                    + count + "...");

            timer2.end();
            Util.printToSystemOutWithWallClockTimePrefix("T1: " + timer2);
            timer2.reset();
            timer2.start();
            String smtStr = buildSMTDescriptionForTseitinEncoding(
                    declarationStr, assertPartition.toString());
            timer2.end();
            Util.printToSystemOutWithWallClockTimePrefix("T2: " + timer2);
            timer2.reset();
            timer2.start();
            String tseitingStr = z3.solve2(smtStr);
            timer2.end();
            Util.printToSystemOutWithWallClockTimePrefix("T3: " + timer2);
            timer2.reset();
            timer2.start();

            TseitinParser parser = parseTseitinStr(tseitingStr, count);
            timer2.end();
            Util.printToSystemOutWithWallClockTimePrefix("T4: " + timer2);
            timer2.reset();
            timer2.start();
            Formula partitionFormula = parser.getRootFormula();
            timer2.end();
            Util.printToSystemOutWithWallClockTimePrefix("T5: " + timer2);
            timer2.reset();
            timer2.start();

            tseitinPartitions.put(partition, partitionFormula);
            timer2.end();
            Util.printToSystemOutWithWallClockTimePrefix("T6: " + timer2);
            timer2.reset();
            timer2.start();

            if (SuraqOptions.getInstance().getCheckTseitin()) {
                Util.printToSystemOutWithWallClockTimePrefix("      test if tseitin encoding is correct...");
                if (!Util.checkFormulaImplication(partitionFormula,
                        assertPartitionFormulas.get(count)))
                    throw new RuntimeException("Tseitin encoding incorrect.");
                Util.printToSystemOutWithWallClockTimePrefix("      ...test finished");
            }
            timer2.end();
            Util.printToSystemOutWithWallClockTimePrefix("T7: " + timer2);
            timer2.reset();
            timer2.start();

            onePartitionTimer.stop();
            Util.printToSystemOutWithWallClockTimePrefix(" Done. ("
                    + onePartitionTimer + ")");
            count++;

        }
    }

    /**
     * Performs the tseitin encoding for each partition. This method does not
     * use the Z3 solver. Adds the encoding for each tseitin variable in the
     * <code>tseitinEncoding</code> map and returns the new encoded partitions.
     * 
     * @return the tseitin encoded partitions
     * 
     */
    private void performTseitinEncodingWithoutZ3() {

        Timer onePartitionTimer = new Timer();

        // SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type,
        // SuraqOptions.getZ3_4Path());

        for (int count = 1; count <= assertPartitionFormulas.size(); count++) {
            onePartitionTimer.reset();
            onePartitionTimer.start();
            Util.printToSystemOutWithWallClockTimePrefix("    Encoding partition "
                    + count + " of " + assertPartitionFormulas.size() + "...");

            Formula partitionFormula = assertPartitionFormulas.get(count);

            // simplify assert partition

            // String smtStr = "";
            // smtStr += SExpressionConstants.SET_LOGIC_QF_UF.toString();
            // smtStr += SExpressionConstants.SET_OPTION_PRODUCE_MODELS_TRUE
            // .toString();
            // smtStr += SExpressionConstants.DECLARE_SORT_VALUE.toString();
            // smtStr += declarationStr;
            // smtStr += "(assert " + partitionFormula.toString() + " )";
            // smtStr += "(apply (then (! simplify :elim-and true) skip))";
            // smtStr += SExpressionConstants.EXIT.toString();
            //
            // String simpleSmtStr = z3.solve2(smtStr);

            Formula simplifiedPartitionFormula = simplifyWithZ3(partitionFormula);
            assert (Util.checkEquivalenceOfFormulas(partitionFormula,
                    simplifiedPartitionFormula));
            partitionFormula = simplifiedPartitionFormula;
            Util.printToSystemOutWithWallClockTimePrefix("Done simplifying.");

            // TseitinParser parser = parseTseitinStr(simpleSmtStr, count);
            // Util.printToSystemOutWithWallClockTimePrefix("Done parsing simplified partition");
            // assert (parser.getTseitinVariables().size() == 0);

            // partitionFormula = parser.getRootFormula();

            // apply tseitin encoding

            List<OrFormula> clauses = new ArrayList<OrFormula>();
            Map<PropositionalVariable, Formula> encoding = new HashMap<PropositionalVariable, Formula>();
            Map<Formula, PropositionalVariable> done = new HashMap<Formula, PropositionalVariable>();
            // also changes the partitionFormula
            Formula tseitinVar = partitionFormula.tseitinEncode(clauses,
                    encoding, done, count);
            Util.printToSystemOutWithWallClockTimePrefix("Done encoding.");
            assert (Util.isLiteral(tseitinVar));
            tseitinEncoding.putAll(encoding);
            if (tseitinVar instanceof PropositionalVariable)
                tseitinEncoding.put((PropositionalVariable) tseitinVar,
                        partitionFormula);

            List<Formula> disjuncts = new ArrayList<Formula>();
            disjuncts.add(tseitinVar);
            clauses.add(OrFormula.generate(disjuncts));
            Formula encodedPartitionFormula = AndFormula.generate(clauses);

            // DebugHelper.getInstance().formulaToFile(encodedPartitionFormula,
            // "debug-tseitin-encoding.txt");

            if (SuraqOptions.getInstance().getCheckTseitin()) {
                Util.printToSystemOutWithWallClockTimePrefix("      test if tseitin encoding is correct...");
                if (!Util.checkFormulaImplication(encodedPartitionFormula,
                        assertPartitionFormulas.get(count)))
                    throw new RuntimeException("Tseitin encoding incorrect.");
                Util.printToSystemOutWithWallClockTimePrefix("      ...test finished");
            }
            onePartitionTimer.stop();
            Util.printToSystemOutWithWallClockTimePrefix(" Done. ("
                    + onePartitionTimer + ")");
            tseitinPartitions.put(count, encodedPartitionFormula);

        }
    }

    private Map<PropositionalVariable, Formula> proofTransformationAndInterpolation(
            List<PropositionalVariable> controlVars) {
        Timer timer = new Timer();
        Map<Integer, Formula> literalMap = new HashMap<Integer, Formula>();
        Set<VeritProofNode> leaves = null;
        Map<VeritProofNode, VeritProofNode> replacements = null;
        LogicParser newLogicParser = null;
        if (SuraqOptions.getInstance().getUseThisPropProofFile() == null) {

            // assert (proof.checkProof());
            Util.printToSystemOutWithWallClockTimePrefix("  Splitting uncolorable leaves in veriT proof...");
            timer.start();
            replacements = veritProof.splitUncolorableLeaves();
            timer.stop();
            Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                    + ")");
            timer.reset();

            Util.printToSystemOutWithWallClockTimePrefix("  Obtaining new propositional ResProof based on new leaves...");

            // Use the getLeaves() method of the root, in order to avoid
            // getting the leaves of the colorable subproofs as well!
            leaves = veritProof.getRoot().getLeaves();

            // Now the original veritProof is no longer need. Let it be garbage
            // collected.
            Util.printToSystemOutWithWallClockTimePrefix("    Killing reference to original veriT proof.");
            veritProof = null;
            // Hint to the garbage collector:
            System.gc();
            timer.start();
        } else {
            Util.printToSystemOutWithWallClockTimePrefix("Using propositional proof from file: "
                    + SuraqOptions.getInstance().getUseThisPropProofFile());
            Set<PropositionalVariable> propVars = new HashSet<PropositionalVariable>();
            Set<DomainVariable> domainVars = new HashSet<DomainVariable>();
            Set<UninterpretedFunction> functions = new HashSet<UninterpretedFunction>();
            propVars.addAll(logicParser.getBoolVariables());
            propVars.addAll(tseitinEncoding.keySet());
            domainVars.addAll(logicParser.getDomainVariables());
            functions.addAll(logicParser.getFunctions());
            for (Formula constraint : constraints) {
                constraint.getDomainVariables(domainVars,
                        new HashSet<SMTLibObject>());
            }
            for (ArrayVariable arrayVar : logicParser.getArrayVariables()) {
                functions.add(UninterpretedFunction.create(
                        arrayVar.getVarName(), 1,
                        SExpressionConstants.VALUE_TYPE));
            }
            for (Token nodepVar : noDependenceVarsCopies.keySet()) {
                for (Term term : noDependenceVarsCopies.get(nodepVar)) {
                    if (term instanceof DomainVariable)
                        domainVars.add((DomainVariable) term);
                    if (term instanceof PropositionalVariable)
                        propVars.add((PropositionalVariable) term);
                }
            }
            for (Token functionName : noDependenceFunctionsCopies.keySet()) {
                for (UninterpretedFunction function : noDependenceFunctionsCopies
                        .get(functionName))
                    functions.add(function);
            }
            newLogicParser = new LogicParser(propVars, domainVars, functions);
        }

        ResProof resProof = null;
        try {
            resProof = ResProof.create(leaves, replacements, literalMap,
                    newLogicParser);
        } catch (IOException exc) {
            System.out.println("IOException during creation of resProof");
            throw new RuntimeException(exc);
        }
        assert (resProof != null);
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("  Done. (" + timer + ")");
        timer.reset();

        Util.printToSystemOutWithWallClockTimePrefix("Dumping resProof.");
        resProof.dumpProof("resProof.txt");
        Util.printToSystemOutWithWallClockTimePrefix("Done");

        Util.printToSystemOutWithWallClockTimePrefix("Size of ResProof: "
                + Util.largeNumberFormatter.format(resProof.size()));

        System.gc();
        Util.printMemoryInformation();

        Util.printToSystemOutWithWallClockTimePrefix("  Processing resolution proof...");
        timer.start();
        // Util.printToSystemOutWithWallClockTimePrefix("    Checking resolution proof.");
        // assert(resProof.checkProof(false));
        // Util.printToSystemOutWithWallClockTimePrefix("    Done.");
        Util.printToSystemOutWithWallClockTimePrefix("    Making it local first.");
        boolean checkResult = resProof.makeLocalFirst(true, false, false);
        assert (checkResult);
        Util.printToSystemOutWithWallClockTimePrefix("    Done.");
        Util.printToSystemOutWithWallClockTimePrefix("Size of ResProof: "
                + Util.largeNumberFormatter.format(resProof.size()));
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");
        timer.reset();
        Util.printToSystemOutWithWallClockTimePrefix("    Recovering.");
        Map<ResNode, TransformedZ3Proof> cache = new HashMap<ResNode, TransformedZ3Proof>();
        TransformedZ3Proof recoveredProof = new TransformedZ3Proof(
                resProof.getRoot(), literalMap, cache);

        // create ITE-tree for every control signal
        Util.printToSystemOutWithWallClockTimePrefix("  Compute interpolants...");
        timer.start();
        Map<PropositionalVariable, Formula> iteTrees = recoveredProof
                .createITETrees(controlVars, tseitinEncoding);
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");
        timer.reset();

        return iteTrees;
    }

    @SuppressWarnings("unused")
    @Deprecated
    private Map<PropositionalVariable, Formula> proofTransformationAndInterpolation(
            Z3Proof rootProof, List<PropositionalVariable> controlVars) {

        Timer timer = new Timer();
        // assert (rootProof.checkZ3ProofNodeRecursive);

        // try {
        // File prooffile = new File("proofTemp.txt");
        // FileWriter fstream = new FileWriter(prooffile);
        // BufferedWriter proofFilewriter = new BufferedWriter(fstream);
        // proofFilewriter.write(rootProof.prettyPrint());
        // proofFilewriter.close();
        // } catch (IOException exc) {
        // System.err.println("Error while writing to proof file.");
        // exc.printStackTrace();
        // noErrors = false;
        // }

        printProofStats(rootProof);

        Util.printToSystemOutWithWallClockTimePrefix("  Computing parent nodes...");
        timer.start();
        rootProof.computeParents();
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");
        timer.reset();
        // assert (rootProof.checkZ3ProofNodeRecursive());

        dealWithBadLiteralHypotheses(rootProof);
        printProofStats(rootProof);

        // timer.start();
        // int all_nodes_size = rootProof.allNodes().size();
        // timer.end();
        // Util.printToSystemOutWithWallClockTimePrefix("  All nodes size: " +
        // all_nodes_size);
        // Util.printToSystemOutWithWallClockTimePrefix("  (computed in " +
        // timer + ")");

        // Util.printToSystemOutWithWallClockTimePrefix("  Local lemmas to assertions...");
        // timer.start();
        // rootProof.localLemmasToAssertions();
        // timer.end();
        // Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer +
        // ")");
        // timer.reset();
        // // assert (rootProof.checkZ3ProofNodeRecursive());
        // timer.start();
        // Util.printToSystemOutWithWallClockTimePrefix("    Proof DAG size: " +
        // rootProof.size(false));
        // timer.end();
        // Util.printToSystemOutWithWallClockTimePrefix("      Size computed in "
        // + timer);
        // timer.reset();
        // timer.start();
        // Util.printToSystemOutWithWallClockTimePrefix("    Proof size after unwinding DAG: "
        // + rootProof.size(true));
        // timer.end();
        // Util.printToSystemOutWithWallClockTimePrefix("      Size computed in "
        // + timer);
        // timer.reset();
        // Util.printToSystemOutWithWallClockTimePrefix();

        Util.printToSystemOutWithWallClockTimePrefix("  Remove local sub-proofs...");
        timer.start();
        rootProof.removeLocalSubProofs();
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");
        timer.reset();
        // assert (rootProof.checkZ3ProofNodeRecursive());
        printProofStats(rootProof);

        // Util.printToSystemOutWithWallClockTimePrefix("Num Instances: " +
        // Z3Proof.numInstances());
        Util.printToSystemOutWithWallClockTimePrefix("  Conversion to transformed z3 proof...");
        timer.start();
        TransformedZ3Proof transformedZ3Proof = TransformedZ3Proof
                .convertToTransformedZ3Proof(rootProof);
        rootProof = null; // Allow this to be garbage collected
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");
        timer.reset();
        printProofStats(transformedZ3Proof);

        /*
         * Util.printToSystemOutWithWallClockTimePrefix("Num Instances: " +
         * Z3Proof.numInstances()); try { File smtfile = new
         * File("proofTemp.txt"); FileWriter fstream = new FileWriter(smtfile);
         * BufferedWriter smtfilewriter = new BufferedWriter(fstream);
         * rootProof.resetMarks(); smtfilewriter.write(rootProof.prettyPrint());
         * smtfilewriter.close(); } catch (IOException exc) {
         * System.err.println("Error while writing to smtfile.");
         * exc.printStackTrace(); noErrors = false; }
         */
        // assert (transformedZ3Proof.checkZ3ProofNodeRecursive());

        Util.printToSystemOutWithWallClockTimePrefix("  To local proof...");
        timer.start();
        transformedZ3Proof.toLocalProof();
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");
        timer.reset();
        // assert (transformedZ3Proof.checkZ3ProofNodeRecursive());
        assert (transformedZ3Proof.isLocal());
        printProofStats(transformedZ3Proof);
        // System.out
        // .println("----Check:"
        // + transformedZ3Proof
        // .checkLeafsAgainstOriginalFormula(this.assertPartitionFormulas));
        Util.printToSystemOutWithWallClockTimePrefix("  To resolution proof...");
        timer.start();
        transformedZ3Proof.toResolutionProof();
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");
        timer.reset();
        printProofStats(transformedZ3Proof);
        // System.out
        // .println("----Check:"
        // + transformedZ3Proof
        // .checkLeafsAgainstOriginalFormula(this.assertPartitionFormulas));

        // START: ASHUTOSH code
        Util.printToSystemOutWithWallClockTimePrefix("  To resolution proof format...");
        timer.start();
        ResProof resolutionProof = Util
                .createResolutionProof(transformedZ3Proof);
        transformedZ3Proof = null; // Allow this to be garbage collected
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");
        timer.reset();

        Util.printToSystemOutWithWallClockTimePrefix("  Check and transform resolution proof...");
        timer.start();
        // resolutionProof.dumpProof();
        resolutionProof.checkProof(false);
        resolutionProof.rmDoubleLits();
        resolutionProof.checkProof(false);
        resolutionProof.deLocalizeProof();
        resolutionProof.checkProof(false);
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");
        timer.reset();
        // END: ASHUTOSH code

        // Transform back into Z3Proof format
        Util.printToSystemOutWithWallClockTimePrefix("  Recover resolution proof...");
        timer.start();
        TransformedZ3Proof recoveredProof = new TransformedZ3Proof(
                resolutionProof.getRoot(), Util.getLiteralMap(), null);
        resolutionProof = null; // Allow this to be garbage collected
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");
        timer.reset();
        printProofStats(recoveredProof);
        // System.out
        // .println("----Check:"
        // + recoveredProof
        // .checkLeafsAgainstOriginalFormula(this.assertPartitionFormulas));

        // create ITE-tree for every control signal
        Util.printToSystemOutWithWallClockTimePrefix("  Compute interpolants...");
        timer.start();
        Map<PropositionalVariable, Formula> iteTrees = recoveredProof
                .createITETrees(controlVars, tseitinEncoding);
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");
        timer.reset();

        return iteTrees;
    }

    /**
     * @param rootProof
     */
    @Deprecated
    private void dealWithBadLiteralHypotheses(Z3Proof rootProof) {
        Timer timer = new Timer();
        timer.start();

        Util.printToSystemOutWithWallClockTimePrefix("  Starting to deal with bad-literal hypotheses...");

        // Find all bad literal hypotheses
        Set<Z3Proof> leafs = rootProof.allLeafs();
        Set<Z3Proof> badLiteralHypotheses = new HashSet<Z3Proof>(leafs.size());
        for (Z3Proof leaf : leafs) {
            if (leaf.getProofType().equals(SExpressionConstants.ASSERTED))
                continue;
            if (leaf.getProofType().equals(SExpressionConstants.COMMUTATIVITY))
                continue;
            assert (leaf.getProofType().equals(SExpressionConstants.HYPOTHESIS));
            assert (Util.isLiteral(leaf.getConsequent()));
            if (Util.containsBadLiteral(leaf.getConsequent()
                    .transformToConsequentsForm()))
                badLiteralHypotheses.add(leaf);
        }
        leafs = null; // Allow this to be garbage collected

        Util.printToSystemOutWithWallClockTimePrefix("    Found "
                + badLiteralHypotheses.size()
                + " bad-literal hypotheses. Current timer: " + timer);

        Set<Formula> badLiterals = new HashSet<Formula>();
        for (Z3Proof badLiteralHypothesis : badLiteralHypotheses)
            badLiterals.add(badLiteralHypothesis.getConsequent());

        Util.printToSystemOutWithWallClockTimePrefix("    These consist of "
                + badLiterals.size() + " different bad literals.");
        Util.printToSystemOutWithWallClockTimePrefix("    Now looking for IFF nodes for all these formulas. Current timer: "
                + timer);

        int foundCounter = 0;
        int literalCount = 0;
        for (Formula badLiteral : badLiterals) {
            Set<Z3Proof> iffNodes = rootProof.findIffNodes(badLiteral);
            Util.printToSystemOutWithWallClockTimePrefix("      Literal "
                    + ++literalCount + ": "
                    + Util.formulaToStringWithoutNewlines(badLiteral));
            Util.printToSystemOutWithWallClockTimePrefix("      Found "
                    + iffNodes.size() + " IFF nodes. Current timer: " + timer);
            Set<Z3Proof> unconditionalIffNodes = new HashSet<Z3Proof>(
                    iffNodes.size());
            boolean found = false;
            for (Z3Proof iffNode : iffNodes) {
                Set<Z3Proof> iffNodeHypotheses = iffNode.getHypotheses();
                if (iffNodeHypotheses.isEmpty()) {
                    unconditionalIffNodes.add(iffNode);
                    found = true;
                    break;
                } else {
                    Util.printToSystemOutWithWallClockTimePrefix("        Found "
                            + iffNodeHypotheses.size()
                            + " hypotheses for IFF node. Size: "
                            + iffNode.size());
                    if (iffNodeHypotheses.size() == 3)
                        assert (iffNodeHypotheses.size() == 3);
                }

            }
            if (found) {
                Util.printToSystemOutWithWallClockTimePrefix("      Unconditional node found. Current timer: "
                        + timer);
                foundCounter++;
            } else {
                Util.printToSystemOutWithWallClockTimePrefix("      NO unconditional node found. Current timer: "
                        + timer);
            }

        }
        Util.printToSystemOutWithWallClockTimePrefix("      Found unconditional nodes for "
                + foundCounter
                + " literals, out of "
                + badLiterals.size()
                + " literals in total. Current timer: " + timer);
        assert (foundCounter == badLiterals.size());

        // Deal with each bad literal hypothesis
        for (Z3Proof badLiteralHypothesis : badLiteralHypotheses) {
            Timer oneHypTimer = new Timer();
            oneHypTimer.start();
            assert (badLiteralHypothesis != null);
            oneHypTimer.stop();
            Util.printToSystemOutWithWallClockTimePrefix("    Update complete. ("
                    + oneHypTimer + ")");
            System.out.println();
        }

        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("  Done with all bad-literal hypotheses. (Overall time: "
                + timer + ")");
    }

    /**
     * Run synthesis in iterative mode.
     * 
     * @throws SuraqException
     */
    private void runIterative() throws SuraqException {
        assert (VeriTSolver.isActive());

        SuraqOptions options = SuraqOptions.getInstance();
        File sourceFile = new File(options.getInput());

        Util.printMemoryInformation();
        Util.printToSystemOutWithWallClockTimePrefix("start input transformations");
        Timer inputTransformationTimer = new Timer();
        parseInput();

        inputTransformationTimer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("finished input transformations in "
                + inputTransformationTimer + ".\n");
        Util.printMemoryInformation();

        mainFormula = performFormulaReductions();
        List<PropositionalVariable> controlVariables = logicParser
                .getControlVariables();
        Map<PropositionalVariable, Formula> interpolants = new HashMap<PropositionalVariable, Formula>(
                2 * controlVariables.size());

        int numControlSignals = controlVariables.size();
        Util.printToSystemOutWithWallClockTimePrefix("Starting iterative interpolant computation");
        // Main loop where one interpolant per iteration is computed
        for (int count = 0; count < numControlSignals; count++) {

            Util.printToSystemOutWithWallClockTimePrefix("##########################################");
            Util.printToSystemOutWithWallClockTimePrefix("Iteration "
                    + (count + 1));
            Util.printToSystemOutWithWallClockTimePrefix("Computing witness function for signal '"
                    + controlVariables.get(0) + "'.");

            Util.printToSystemOutWithWallClockTimePrefix("Preparing output expressions...");
            prepareOutputExpressions(mainFormula, controlVariables);
            Util.printToSystemOutWithWallClockTimePrefix("Done.");

            Util.printToSystemOutWithWallClockTimePrefix("  build function and variable lists for parser");
            propositionalVars.clear();
            mainFormula.getPropositionalVariables(propositionalVars,
                    new HashSet<SMTLibObject>());
            domainVars.clear();
            mainFormula.getDomainVariables(domainVars,
                    new HashSet<SMTLibObject>());
            arrayVars.clear();
            mainFormula.getArrayVariables(arrayVars,
                    new HashSet<SMTLibObject>());
            uninterpretedFunctions.clear();
            mainFormula.getUninterpretedFunctions(uninterpretedFunctions,
                    new HashSet<SMTLibObject>());
            for (Map.Entry<Token, List<Term>> varList : noDependenceVarsCopies
                    .entrySet()) {
                assert (varList.getValue() != null);
                assert (varList.getValue().size() > 0);

                Term first = varList.getValue().get(0);

                if (first instanceof DomainVariable)
                    for (Term var : varList.getValue())
                        domainVars.add((DomainVariable) var);

                if (first instanceof PropositionalVariable)
                    for (Term var : varList.getValue())
                        propositionalVars.add((PropositionalVariable) var);

                if (first instanceof ArrayVariable)
                    for (Term var : varList.getValue())
                        arrayVars.add((ArrayVariable) var);
            }
            for (Map.Entry<Token, List<UninterpretedFunction>> functionList : noDependenceFunctionsCopies
                    .entrySet())
                uninterpretedFunctions.addAll(functionList.getValue());

            if (options.getTseitinType() == SuraqOptions.TSEITIN_WITHOUT_Z3) {
                Util.printToSystemOutWithWallClockTimePrefix("  Performing tseitin encoding without Z3...");
                performTseitinEncodingWithoutZ3();
            } else {
                Util.printToSystemOutWithWallClockTimePrefix("  Performing tseitin encoding with Z3...");
                performTseitinEncodingWithZ3();
            }
            Util.printToSystemOutWithWallClockTimePrefix("  All partitions done.");

            BufferedReader proofReader;
            Util.printToSystemOutWithWallClockTimePrefix("start proof calculation.");
            Timer proofcalculationTimer = new Timer();
            proofcalculationTimer.start();

            List<Formula> tseitinPartitionsList = new ArrayList<Formula>(
                    tseitinPartitions.size());
            for (Integer key : tseitinPartitions.keySet())
                tseitinPartitionsList.add(tseitinPartitions.get(key));

            VeriTSolver veriT = new VeriTSolver();
            Timer veritTimer = new Timer();
            veritTimer.start();
            veriT.solve(tseitinPartitionsList);
            veritTimer.stop();
            Util.printToSystemOutWithWallClockTimePrefix("VeriTSolver returned!");
            Util.printToSystemOutWithWallClockTimePrefix("Solving and proof production took "
                    + veritTimer.toString() + ".");
            try {
                proofReader = veriT.getStream();
            } catch (FileNotFoundException exc) {
                throw new RuntimeException(exc);
            }

            VeriTParser veriTParser;
            veriTParser = new VeriTParser(proofReader, mainFormula,
                    tseitinEncoding.keySet(), noDependenceVarsCopies.values(),
                    noDependenceFunctionsCopies);
            Util.printMemoryInformation();
            if (!options.getCheckProofWhileParsing()) {
                VeritProof.setCheckProofEnabled(false);
                VeritProofNode.setCheckProofNodesEnabled(false);
            }
            Util.printToSystemOutWithWallClockTimePrefix("start to parse proof.");
            Timer parseTimer = new Timer();
            parseTimer.start();
            veriTParser.parse();
            parseTimer.stop();
            Util.printToSystemOutWithWallClockTimePrefix("Done parsing. (Took "
                    + parseTimer.toString() + ")");
            veritProof = veriTParser.getProof();
            assert (veritProof != null);
            Util.printToSystemOutWithWallClockTimePrefix("Proof size: "
                    + Util.largeNumberFormatter.format(veritProof.size()));
            veritProof.removeUnreachableNodes();
            Util.printToSystemOutWithWallClockTimePrefix("Proof size (after removing unreachable nodes): "
                    + Util.largeNumberFormatter.format(veritProof.size()));
            assert (veritProof.checkProof());
            assert (veritProof.hasNoBadLiterals());

            Util.printToSystemOutWithWallClockTimePrefix("Starting to interpolate even vs. odd partitions.");
            Timer interpolationTimer = new Timer();
            interpolationTimer.start();
            Formula interpolant = veritProof
                    .interpolateEvenVsOddPartitions(tseitinPartitions);
            interpolationTimer.stop();
            Util.printToSystemOutWithWallClockTimePrefix("Done interpolation. (Took "
                    + interpolationTimer.toString() + ")");

            Util.printToSystemOutWithWallClockTimePrefix("Backsubsituting Tseitin encoding.");
            Map<Token, Term> substitutionsMap = new HashMap<Token, Term>();
            for (PropositionalVariable tseitinVar : tseitinEncoding.keySet())
                substitutionsMap.put(Token.generate(tseitinVar.getVarName()),
                        FormulaTerm.create(tseitinEncoding.get(tseitinVar)));
            Util.printToSystemOutWithWallClockTimePrefix("Done.");
            Map<SMTLibObject, SMTLibObject> done = new HashMap<SMTLibObject, SMTLibObject>();
            interpolant = interpolant.substituteFormula(substitutionsMap, done);
            // interpolant = simplifyWithZ3(interpolant);
            FormulaSimplifier simplifier = new FormulaSimplifier(interpolant);
            try {
                simplifier.simplify();
            } catch (IOException exc) {
                throw new RuntimeException(
                        "Could not simplify interpolant due to IOException",
                        exc);
            }
            assert (simplifier.checkSimplification());
            interpolant = simplifier.getSimplifiedFormula();
            assert (Util.checkInterpolant(interpolant, assertPartitionFormulas));

            Util.printToSystemOutWithWallClockTimePrefix("Resubstituting...");
            PropositionalVariable currentSignal = controlVariables.remove(0);
            // DEBUG
            File interpolantFile = new File(currentSignal.getVarName()
                    .toString() + ".smt2");
            try {
                FileWriter fwriter = new FileWriter(interpolantFile);
                Util.printToSystemOutWithWallClockTimePrefix("Writing interpolant to "
                        + interpolantFile.toString());
                BufferedWriter writer = new BufferedWriter(fwriter);
                Util.writeFormulaUsingLetExpressions(interpolant, writer);
                writer.close();
                fwriter.close();
            } catch (IOException exc) {
                Util.printToSystemOutWithWallClockTimePrefix("Could not write interpolant to file.");
                exc.printStackTrace();
            }
            // END DEBUG
            interpolants.put(currentSignal, interpolant);
            Map<Token, PropositionalTerm> substMap = new TreeMap<Token, PropositionalTerm>();
            substMap.put(Token.generate(currentSignal.getVarName()),
                    FormulaTerm.create(interpolant));
            done.clear();
            mainFormula = mainFormula.substituteFormula(substMap, done);

            if (count == numControlSignals - 1) {
                // This was the last control signal.
                // mainFormula should now be UNSAT.
                Util.printToSystemOutWithWallClockTimePrefix("Checking if negation of main formula is UNSAT");
                if (!Util.checkUnsat(NotFormula.create(mainFormula))) {
                    noErrors = false;
                    Util.printToSystemOutWithWallClockTimePrefix("ERROR! negation of mainFormula was not UNSAT!");
                } else
                    Util.printToSystemOutWithWallClockTimePrefix("OK! negation of mainFormula is UNSAT.");
            }

            assertPartitionFormulas.clear();
            tseitinPartitions.clear();
            tseitinEncoding.clear();
            declarationStr = "";
        }

        // Done with iterative interpolation

        Util.printToSystemOutWithWallClockTimePrefix("Starting back-substitution");
        for (PropositionalVariable key : interpolants.keySet()) {
            assert (interpolants.get(key) != null);
            Formula interpolant = (Formula) interpolants.get(key)
                    .uninterpretedFunctionsBackToArrayReads(
                            new HashSet<ArrayVariable>(
                                    logicParser.getArrayVariables()),
                            new HashMap<SMTLibObject, SMTLibObject>());
            interpolants.put(key, interpolant);
        }
        // write output file
        try {
            Util.printToSystemOutWithWallClockTimePrefix(" Writing output to file "
                    + options.getOutput());
            FileWriter fstream = new FileWriter(options.getOutput());
            BufferedWriter writer = new BufferedWriter(fstream);
            createOutputFile(sourceFile, interpolants, writer);
            writer.close();
            fstream.close();
        } catch (IOException exc) {
            Util.printToSystemOutWithWallClockTimePrefix("Error while writing to output file: "
                    + options.getOutput());
            exc.printStackTrace();
            noErrors = false;
        }

        if (options.isCheckResult()) {
            Util.printToSystemOutWithWallClockTimePrefix("Starting to check results with z3...");
            Timer checkTimer = new Timer();
            checkTimer.start();
            SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type, "lib/z3/bin/z3");
            z3.solve(new File(options.getOutput()));

            switch (z3.getState()) {
            case SMTSolver.UNSAT:
                Util.printToSystemOutWithWallClockTimePrefix("SUCCESSFULLY MODEL-CHECKED RESULTS WITH Z3! :-)");
                break;
            case SMTSolver.SAT:
                noErrors = false;
                Util.printToSystemOutWithWallClockTimePrefix("ERROR: Z3 tells us SAT. Implementation of control signal is not correct");
                break;
            default:
                noErrors = false;
                Util.printToSystemOutWithWallClockTimePrefix("Z3 OUTCOME ---->  UNKNOWN! CHECK ERROR STREAM.");
            }
            checkTimer.stop();
            Util.printToSystemOutWithWallClockTimePrefix("Check finished in "
                    + checkTimer);
        }

        Util.printToSystemOutWithWallClockTimePrefix(" done!");
        // All done :-)
        overallTimer.stop();
        printEnd(noErrors, overallTimer);
        // System.err.println(Suraq.extTimer);
        return;

    }

    /**
     * @param formula
     * @return
     */
    private Formula simplifyWithZ3(Formula formula) {
        z3 z3 = (at.iaik.suraq.smtsolver.z3) SMTSolver.create(
                SMTSolver.z3_type, SuraqOptions.getZ3_4Path());

        Timer timer = new Timer();
        timer.start();
        Util.printToSystemOutWithWallClockTimePrefix("Simplifying formula.");
        BufferedReader simpliefiedFormulaReader = z3.simplify(formula);
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("Done. (Took "
                + timer.toString() + ")");
        Util.printToSystemOutWithWallClockTimePrefix("Starting parsing.");
        try {
            Set<ArrayVariable> aVars = new HashSet<ArrayVariable>();
            formula.getArrayVariables(aVars, new HashSet<SMTLibObject>());
            Set<PropositionalVariable> pVars = new HashSet<PropositionalVariable>();
            Set<DomainVariable> dVars = new HashSet<DomainVariable>();
            Set<UninterpretedFunction> ufs = new HashSet<UninterpretedFunction>();
            Set<SMTLibObject> done = new HashSet<SMTLibObject>();
            formula.getPropositionalVariables(pVars, done);
            done.clear();
            formula.getDomainVariables(dVars, done);
            done.clear();
            formula.getUninterpretedFunctions(ufs, done);
            done.clear();
            FormulaParser parser = new FormulaParser(pVars, dVars, aVars, ufs,
                    simpliefiedFormulaReader);
            Util.printToSystemOutWithWallClockTimePrefix("Finished parsing SExpressions. Starting to parse formula.");
            parser.parse();
            Formula result = parser.getParsedFormula();
            Util.printToSystemOutWithWallClockTimePrefix("Done.");
            return result;
        } catch (ParseError exc) {
            System.out.println("Parser error.");
            throw new RuntimeException(exc);
        } catch (IOException exc) {
            System.out.println("IOException.");
            throw new RuntimeException(exc);
        }
    }

    /**
     * @see java.lang.Runnable#run()
     */
    @Override
    public void run() {
        overallTimer.start();

        printWelcome();

        SuraqOptions options = SuraqOptions.getInstance();
        if (options.getIterativeInterpolation() == true) {
            Util.printToSystemOutWithWallClockTimePrefix("Running in iterative mode...");
            VeriTSolver.setActive(true);
            try {
                runIterative();
            } catch (SuraqException exc) {
                throw new RuntimeException(exc);
            }
            return;
        }
        if (options.getSolver().toLowerCase().equals("z3")) {
            VeriTSolver.setActive(false);
        } else if (options.getSolver().toLowerCase().equals("verit")) {
            VeriTSolver.setActive(true);
        } else {
            Util.printToSystemOutWithWallClockTimePrefix("WARNING: Unknown solver \""
                    + options.getSolver()
                    + "\" selected. Using veriT per default.");
            VeriTSolver.setActive(true);
        }

        if (VeriTSolver.isActive()) {
            runWithVeriT();
            return;
            // IMPORTANT: Any reference to veriT below is deprecated.
            // When using veriT, everything is done in runWithVeriT.
            // The following usage of veriT in this method is just
            // left-over code, that should now be unreachable.
        }

        assert (!VeriTSolver.isActive());
        assert (options.getSolver().toLowerCase().equals("z3"));
        throw new RuntimeException("Only veriT solver currently supported!");

    }

    /**
     * Main control flow when using veriT.
     */
    private void runWithVeriT() {
        assert (VeriTSolver.isActive());
        SuraqOptions options = SuraqOptions.getInstance();

        File sourceFile = new File(options.getInput());
        List<PropositionalVariable> controlVariables = null;
        Map<PropositionalVariable, Formula> iteTrees = null;

        Util.printMemoryInformation();
        Util.printToSystemOutWithWallClockTimePrefix("start input transformations");
        Timer inputTransformationTimer = new Timer();
        inputTransformationTimer.start();
        inputTransformations(sourceFile);
        controlVariables = logicParser.getControlVariables();
        inputTransformationTimer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("finished input transformations in "
                + inputTransformationTimer + ".\n");
        Util.printMemoryInformation();

        if (options.getUseThisPropProofFile() == null) {
            String providedProofFile = options.getUseThisProofFile();
            Timer veritTimer = new Timer();
            veritTimer.start();
            BufferedReader proofReader;
            if (providedProofFile == null) {
                Util.printToSystemOutWithWallClockTimePrefix("start proof calculation.");
                Timer proofcalculationTimer = new Timer();
                proofcalculationTimer.start();
                List<Formula> tseitinPartitionsList = new ArrayList<Formula>(
                        tseitinPartitions.size());
                for (Integer key : tseitinPartitions.keySet())
                    tseitinPartitionsList.add(tseitinPartitions.get(key));
                VeriTSolver veriT = new VeriTSolver();
                veriT.solve(tseitinPartitionsList);
                Util.printToSystemOutWithWallClockTimePrefix("VeriTSolver returned!");
                veritTimer.stop();
                Util.printToSystemOutWithWallClockTimePrefix("Solving and proof production took "
                        + veritTimer.toString() + ".");
                try {
                    proofReader = veriT.getStream();
                } catch (FileNotFoundException exc) {
                    throw new RuntimeException(exc);
                }
            } else {
                try {
                    proofReader = new BufferedReader(new FileReader(
                            providedProofFile));
                    Util.printToSystemOutWithWallClockTimePrefix("[INFO] Using the following proof file, instead of calling the solver: "
                            + providedProofFile);
                } catch (FileNotFoundException exc) {
                    System.out.println("Proof file not found: "
                            + providedProofFile);
                    throw new RuntimeException(exc);
                }
            }

            VeriTParser veriTParser;
            veriTParser = new VeriTParser(proofReader, mainFormula,
                    tseitinEncoding.keySet(), noDependenceVarsCopies.values(),
                    noDependenceFunctionsCopies);
            Util.printMemoryInformation();
            if (!options.getCheckProofWhileParsing()) {
                VeritProof.setCheckProofEnabled(false);
                VeritProofNode.setCheckProofNodesEnabled(false);
            }
            Util.printToSystemOutWithWallClockTimePrefix("start to parse proof.");
            Timer parseTimer = new Timer();
            parseTimer.start();
            veriTParser.parse();
            parseTimer.stop();
            Util.printToSystemOutWithWallClockTimePrefix("Done parsing. (Took "
                    + parseTimer.toString() + ")");
            veritProof = veriTParser.getProof();
            assert (veritProof != null);
            Util.printToSystemOutWithWallClockTimePrefix("Proof size: "
                    + Util.largeNumberFormatter.format(veritProof.size()));
            veritProof.removeUnreachableNodes();
            Util.printToSystemOutWithWallClockTimePrefix("Proof size (after removing unreachable nodes): "
                    + Util.largeNumberFormatter.format(veritProof.size()));
            assert (veritProof.checkProof());
            assert (veritProof.hasNoBadLiterals());

        }

        if (options.getUseThisPropProofFile() == null) {
            assert (veritProof != null);
            VeritProof.setCheckProofEnabled(true);
            VeritProofNode.setCheckProofNodesEnabled(true);
            Util.printMemoryInformation();
        }
        iteTrees = proofTransformationAndInterpolation(controlVariables);

        Util.printToSystemOutWithWallClockTimePrefix("Starting back-substitution");
        for (PropositionalVariable key : iteTrees.keySet()) {
            assert (iteTrees.get(key) != null);
            Formula iteTree = iteTrees.get(key);
            iteTree = simplifyWithZ3(iteTree);
            iteTree = (Formula) iteTree
                    .uninterpretedFunctionsBackToArrayReads(
                            new HashSet<ArrayVariable>(logicParser
                                    .getArrayVariables()),
                            new HashMap<SMTLibObject, SMTLibObject>());
            iteTrees.put(key, iteTree);
        }

        // write output file
        try {
            Util.printToSystemOutWithWallClockTimePrefix(" Writing output to file "
                    + options.getOutput());
            FileWriter fstream = new FileWriter(options.getOutput());
            BufferedWriter writer = new BufferedWriter(fstream);
            createOutputFile(sourceFile, iteTrees, writer);
            writer.close();
            fstream.close();
        } catch (IOException exc) {
            Util.printToSystemOutWithWallClockTimePrefix("Error while writing to output file: "
                    + options.getOutput());
            exc.printStackTrace();
            noErrors = false;
        }

        overallTimer.stop(); // Don't count time to check results.
        if (options.isCheckResult()) {
            Util.printToSystemOutWithWallClockTimePrefix("Starting to check results with z3...");
            Timer checkTimer = new Timer();
            checkTimer.start();
            SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type, "lib/z3/bin/z3");
            z3.solve(new File(options.getOutput()));

            switch (z3.getState()) {
            case SMTSolver.UNSAT:
                Util.printToSystemOutWithWallClockTimePrefix("SUCCESSFULLY MODEL-CHECKED RESULTS WITH Z3! :-)");
                break;
            case SMTSolver.SAT:
                noErrors = false;
                Util.printToSystemOutWithWallClockTimePrefix("ERROR: Z3 tells us SAT. Implementation of control signal is not correct");
                break;
            default:
                noErrors = false;
                Util.printToSystemOutWithWallClockTimePrefix("Z3 OUTCOME ---->  UNKNOWN! CHECK ERROR STREAM.");
            }
            checkTimer.stop();
            Util.printToSystemOutWithWallClockTimePrefix("Check finished in "
                    + checkTimer);
        }

        Util.printToSystemOutWithWallClockTimePrefix(" done!");
        // All done :-)

        printEnd(noErrors, overallTimer);
        // System.err.println(Suraq.extTimer);
        return;
    }

    /**
     * Forms the file which represents the final result of suraq. The
     * interpolation result for each control signal is inserted in the original
     * input file, and forms the result.
     * 
     * @param interpolationFormulas
     *            Map which contains the interpolation for each control signal
     * @param writer
     *            the writer to write to
     * @return the string from the union of the input file and
     *         control-signal-interpolations.
     * @throws IOException
     * 
     */
    private void createOutputFile(File sourceFile,
            Map<PropositionalVariable, Formula> interpolations, Writer writer)
            throws IOException {

        SExpParser sExpParser = null;
        try {
            sExpParser = new SExpParser(sourceFile);
        } catch (FileNotFoundException exc) {
            System.err.println("ERROR: File " + sourceFile.getPath()
                    + " not found!");
            noErrors = false;
            return;
        } catch (IOException exc) {
            System.err.println("ERROR: Could not read from file "
                    + sourceFile.getPath());
            noErrors = false;
            return;
        }

        try {
            sExpParser.parse();
            assert (sExpParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            noErrors = false;
            return;
        }

        SExpression rootExp = sExpParser.getRootExpr();
        ArrayList<SExpression> children = new ArrayList<SExpression>(
                rootExp.getChildren());

        rootExp.replaceChild(SExpressionConstants.SET_LOGIC_QF_AUFLIA, 0);
        rootExp.addChild(SExpressionConstants.DECLARE_SORT_VALUE, 1);

        int count = 1;
        SExpression lastDeclare = null;
        for (SExpression child : children) {
            // if (child.toString().contains("declare-fun")) {
            // String newChild = child.toString().replace("Control", "Bool")
            // .replace(":no_dependence", " ");
            // newChild = newChild.replace("\n\n", "\n");
            //
            // rootExp.replaceChild(SExpression.fromString(newChild), count);
            // lastDeclare = rootExp.getChildren().get(count);
            // }
            child.changeControlAndNoDepDefs();
            if (child.isDeclareFun())
                lastDeclare = rootExp.getChildren().get(count);

            // negate assert formulas
            if (child.isAssert()) {

                assert (child.getChildren().size() == 2);

                SExpression assertFormula = child.getChildren().get(1);

                SExpression negatedAssertFormula = new SExpression(
                        SExpressionConstants.NOT, assertFormula);

                SExpression negatedAssert = new SExpression(
                        SExpressionConstants.ASSERT, negatedAssertFormula);

                rootExp.replaceChild(negatedAssert, count);
            }
            count++;
        }

        // Add constraints for new variables
        insertConstraintDeclarations(rootExp, lastDeclare);
        SExpression constraintExp = new SExpression(
                SExpressionConstants.ASSERT, AndFormula
                        .generate(new ArrayList<Formula>(this.constraints))
                        .uninterpretedFunctionsBackToArrayReads(
                                new HashSet<ArrayVariable>(
                                        logicParser.getArrayVariables()),
                                new HashMap<SMTLibObject, SMTLibObject>())
                        .toSmtlibV2());
        rootExp.addChild(constraintExp);

        for (SExpression child : rootExp.getChildren())
            child.writeTo(writer);

        // add new assert formulas for each control signal
        for (Map.Entry<PropositionalVariable, Formula> entry : interpolations
                .entrySet()) {
            PropositionalVariable controlSignal = entry.getKey();
            Formula controlFormula = entry.getValue();

            writer.write("(assert (= ");
            writer.write(controlSignal.toString());
            writer.write(" \n");
            Util.writeFormulaUsingLetExpressions(controlFormula, writer);
            writer.write("\n))");
        }

        writer.write(SExpressionConstants.CHECK_SAT.toString());

    }

    /**
     * @param rootExp
     * @param lastDeclare
     */
    private void insertConstraintDeclarations(SExpression rootExp,
            SExpression lastDeclare) {

        assert (constraints != null);

        SExpression currentLast = lastDeclare;

        if (constraints.isEmpty())
            return;

        assert (constraints.size() > 0);
        AndFormula constraint = AndFormula.generate(new ArrayList<Formula>(
                constraints));

        // Adding declare-fun for array variables
        Set<ArrayVariable> localArrayVars = new HashSet<ArrayVariable>();
        constraint.getArrayVariables(localArrayVars,
                new HashSet<SMTLibObject>());
        localArrayVars.removeAll(this.logicParser.getArrayVariables());
        for (ArrayVariable var : localArrayVars) {
            SExpression declare = SExpression.makeDeclareFun(
                    Token.generate(var.getVarName()),
                    SExpressionConstants.ARRAY_TYPE, 0);
            rootExp.insertChildAfter(declare, currentLast);
            currentLast = declare;
        }

        // Adding declare-fun for domain variables
        Set<DomainVariable> localDomainVars = new HashSet<DomainVariable>();
        constraint.getDomainVariables(localDomainVars,
                new HashSet<SMTLibObject>());
        localDomainVars.removeAll(this.logicParser.getDomainVariables());
        for (DomainVariable var : localDomainVars) {
            SExpression declare = SExpression.makeDeclareFun(
                    Token.generate(var.getVarName()),
                    SExpressionConstants.VALUE_TYPE, 0);
            rootExp.insertChildAfter(declare, currentLast);
            currentLast = declare;
        }

        // Adding declare-fun for propositional variables
        Set<PropositionalVariable> localPropositionalVars = new HashSet<PropositionalVariable>();
        constraint.getPropositionalVariables(localPropositionalVars,
                new HashSet<SMTLibObject>());
        localPropositionalVars.removeAll(this.logicParser.getBoolVariables());
        localPropositionalVars
                .removeAll(this.logicParser.getControlVariables());
        for (PropositionalVariable var : localPropositionalVars) {
            SExpression declare = SExpression.makeDeclareFun(
                    Token.generate(var.getVarName()),
                    SExpressionConstants.BOOL_TYPE, 0);
            rootExp.insertChildAfter(declare, currentLast);
            currentLast = declare;
        }

    }

    /**
     * Parses <code>tseitinStr</code> into a formula.
     * 
     * @param tseitinStr
     *            output string of the z3 after applying tseitin encoding
     * @param partition
     *            the partition of the tseitin string
     * @return the parser that parsed the formula.
     * 
     */
    private TseitinParser parseTseitinStr(String tseitinStr, int partition) {
        SExpParser sExpParser = new SExpParser(tseitinStr);
        try {
            sExpParser.parse();
            assert (sExpParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            throw new RuntimeException(
                    "S-Expression parse error. Cannot continue.", exc);
        }

        SExpression rootExp = sExpParser.getRootExpr();

        TseitinParser tseitinParser = new TseitinParser(rootExp, domainVars,
                propositionalVars, arrayVars, uninterpretedFunctions, partition);
        try {
            tseitinParser.parse();
            assert (tseitinParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            throw new RuntimeException(
                    "Tseitin encoding parse error. Cannot continue.", exc);
        }
        tseitinEncoding.putAll(tseitinParser.getTseitinEncoding());

        return tseitinParser;
    }

    /**
     * Creates an SMT Description from the tseitin assert partitions. Adds
     * entries in the <code>tseitinEncoding</code> map, for each tseitin
     * variable the corresponding formula.
     * 
     * @param declarationStr
     *            declarations of the SMT Description
     * @param tseitinAssertPartitions
     *            tseitin assert partitions
     * @return SMT description to proof
     * 
     */
    @SuppressWarnings("unused")
    @Deprecated
    private String buildSMTDescriptionFromTseitinPartitions(
            String declarationStr, Map<Integer, Formula> tseitinPartitions) {

        StringBuilder smtStr = new StringBuilder();

        smtStr.append(SExpressionConstants.SET_LOGIC_QF_UF.toString());
        if (!VeriTSolver.isActive()) {
            smtStr.append(SExpressionConstants.AUTO_CONFIG_FALSE.toString());
            smtStr.append(SExpressionConstants.PROOF_MODE_2.toString());
            smtStr.append(SExpressionConstants.SET_OPTION_PROPAGATE_BOOLEANS_FALSE
                    .toString());
            smtStr.append(SExpressionConstants.SET_OPTION_PROPAGATE_VALUES_FALSE
                    .toString());
        }
        smtStr.append(SExpressionConstants.DECLARE_SORT_VALUE.toString());
        smtStr.append(declarationStr);

        // declarations for tseitin variables
        for (PropositionalVariable var : tseitinEncoding.keySet())
            smtStr.append(SExpression.makeDeclareFun(
                    Token.generate(var.getVarName()),
                    SExpressionConstants.BOOL_TYPE, 0));

        for (int count : tseitinPartitions.keySet()) {
            Formula tseitinPartition = tseitinPartitions.get(count);
            smtStr.append("(assert " + tseitinPartition.toString() + ")");
        }

        smtStr.append(SExpressionConstants.CHECK_SAT.toString());

        if (!VeriTSolver.isActive())
            smtStr.append(SExpressionConstants.GET_PROOF.toString());
        smtStr.append(SExpressionConstants.EXIT.toString());

        return smtStr.toString();
    }

    @SuppressWarnings("unused")
    @Deprecated
    private String buildSMTDescriptionWithoutTsetin(String declarationStr) {

        StringBuffer smtStr = new StringBuffer();

        smtStr.append(SExpressionConstants.SET_LOGIC_QF_UF.toString());
        if (!VeriTSolver.isActive())
            smtStr.append(SExpressionConstants.AUTO_CONFIG_FALSE.toString());
        smtStr.append(SExpressionConstants.PROOF_MODE_2.toString());
        if (!VeriTSolver.isActive())
            smtStr.append(SExpressionConstants.SET_OPTION_PROPAGATE_BOOLEANS_FALSE
                    .toString());
        smtStr.append(SExpressionConstants.SET_OPTION_PROPAGATE_VALUES_FALSE
                .toString());
        // if(!VeriTSolver.isActive())
        smtStr.append(SExpressionConstants.DECLARE_SORT_VALUE.toString());

        smtStr.append(declarationStr);

        for (SExpression assertPartition : assertPartitionList) {
            // smtStr.append("(assert " + assertPartition + ")");
            smtStr.append(assertPartition);
        }

        smtStr.append(SExpressionConstants.CHECK_SAT.toString());
        if (!VeriTSolver.isActive()) {
            // ???
        }
        smtStr.append(SExpressionConstants.GET_PROOF.toString());
        smtStr.append(SExpressionConstants.EXIT.toString());

        return smtStr.toString();
    }

    /**
     * Creates an SMT Description from the simplified assert partitions.
     * 
     * @param declarationStr
     *            declarations of the SMT Description
     * @param simplifiedAssertPartitions
     *            simplified assert partitions
     * @return SMT description to proof
     * 
     */
    @SuppressWarnings("unused")
    @Deprecated
    private String buildProofSMTDescription(String declarationStr,
            List<String> simplifiedAssertPartitions) {
        String smtStr = "";

        smtStr += SExpressionConstants.SET_LOGIC_QF_UF.toString();
        smtStr += SExpressionConstants.AUTO_CONFIG_FALSE.toString();
        smtStr += SExpressionConstants.PROOF_MODE_2.toString();
        smtStr += SExpressionConstants.SET_OPTION_PROPAGATE_BOOLEANS_FALSE
                .toString();
        smtStr += SExpressionConstants.SET_OPTION_PROPAGATE_VALUES_FALSE
                .toString();
        smtStr += SExpressionConstants.DECLARE_SORT_VALUE.toString();

        smtStr += declarationStr;

        // create assert partition for every simplified partition
        for (String partition : simplifiedAssertPartitions) {
            SExpression expr = new SExpression(Token.generate("assert"),
                    SExpression.fromString(partition));
            smtStr += expr.toString();
        }

        smtStr += SExpressionConstants.CHECK_SAT.toString();
        smtStr += SExpressionConstants.GET_PROOF.toString();
        smtStr += SExpressionConstants.EXIT.toString();

        return smtStr;
    }

    /**
     * Creates an SMT description for an tseitin-cnf operation
     * 
     * @param declarationStr
     *            declarations of the SMT description
     * @param assertPartition
     *            partition to be transformed by tseitin-encoding
     * @return SMT description of tseitin-encoding operation
     * 
     */
    private String buildSMTDescriptionForTseitinEncoding(String declarationStr,
            String assertPartition) {
        String smtStr = "";

        smtStr += SExpressionConstants.SET_LOGIC_QF_UF.toString();
        smtStr += SExpressionConstants.SET_OPTION_PRODUCE_MODELS_TRUE
                .toString();
        smtStr += SExpressionConstants.DECLARE_SORT_VALUE.toString();

        smtStr += declarationStr;

        smtStr += assertPartition;

        smtStr += SExpressionConstants.APPLY_TSEITIN.toString();

        smtStr += SExpressionConstants.EXIT.toString();

        return smtStr;
    }

    /**
     * Takes the main formula from <code>logicParser</code> and performs the
     * reductions on it (arrays, ITEs, ...)
     * 
     * @return the reduced formula.
     */
    private Formula performFormulaReductions() throws SuraqException {
        Suraq.extTimer.stopReset("<doMainWork>");
        Timer timer = new Timer();
        Formula formula = logicParser.getMainFormula();

        // Output statistics
        List<ArrayVariable> arrayVars2 = logicParser.getArrayVariables();
        List<DomainVariable> domainVars = logicParser.getDomainVariables();
        List<PropositionalVariable> propVars = logicParser.getBoolVariables();
        List<Token> nodepVars = logicParser.getNoDependenceVariables();

        int numDepvars = 0;
        for (ArrayVariable var : arrayVars2) {
            if (!nodepVars.contains(Token.generate(var.getVarName())))
                numDepvars++;
        }
        for (DomainVariable var : domainVars) {
            if (!nodepVars.contains(Token.generate(var.getVarName())))
                numDepvars++;
        }
        for (PropositionalVariable var : propVars) {
            if (!nodepVars.contains(Token.generate(var.getVarName())))
                numDepvars++;
        }
        Util.printToSystemOutWithWallClockTimePrefix("[INFO] The following number refer to variables DECLARED in the input file.");
        Util.printToSystemOutWithWallClockTimePrefix("[INFO] They are not necessarily actually USED in the formula.");
        Util.printToSystemOutWithWallClockTimePrefix("Number of variables on which the controllers CAN    depend: "
                + numDepvars);
        Util.printToSystemOutWithWallClockTimePrefix("Number of variables on which the controllers CANNOT depend: "
                + nodepVars.size());
        Util.printToSystemOutWithWallClockTimePrefix("Number of (all) array variables: "
                + arrayVars2.size());

        Set<UninterpretedFunction> ufs = new HashSet<UninterpretedFunction>();
        formula.getUninterpretedFunctions(ufs, new HashSet<SMTLibObject>());
        int numUfs = 0;
        int numUps = 0;
        for (UninterpretedFunction function : ufs) {
            if (function.getType().equals(SExpressionConstants.BOOL_TYPE))
                numUps++;
            if (function.getType().equals(SExpressionConstants.VALUE_TYPE))
                numUfs++;
        }
        Util.printToSystemOutWithWallClockTimePrefix("Number of uninterpreted functions: "
                + numUfs);
        Util.printToSystemOutWithWallClockTimePrefix("Number of uninterpreted predicates: "
                + numUps);

        // Util.writeFormulaToFile(formula, "afterNothing.smt2", false, false);
        // // DEBUG

        // Flattening formula, because macros cause problems when
        // replacing arrays with uninterpreted functions
        // (functions cannot be macro parameters)
        Util.printToSystemOutWithWallClockTimePrefix("  Flattening formula...");
        timer.start();
        formula = formula.flatten();
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");

        // Util.writeFormulaToFile(formula, "afterFlatten.smt2", false, false);
        // // DEBUG

        BigInteger treeSize = formula.size(true,
                new HashMap<Formula, BigInteger>());
        BigInteger dagSize = formula.size(false,
                new HashMap<Formula, BigInteger>());

        Util.printToSystemOutWithWallClockTimePrefix("Formula DAG  size: "
                + dagSize.toString());
        Util.printToSystemOutWithWallClockTimePrefix("Formula tree size: "
                + treeSize.toString());

        Set<FunctionMacro> macros = new HashSet<FunctionMacro>();
        formula.getFunctionMacros(macros, new HashSet<SMTLibObject>());
        assert (macros.isEmpty());
        noDependenceVars = new HashSet<Token>(
                logicParser.getNoDependenceVariables());

        Set<Formula> constraints = new HashSet<Formula>();
        Util.printToSystemOutWithWallClockTimePrefix("  Removing array ITEs...");
        timer.reset();
        timer.start();
        formula = formula
                .removeArrayITE(formula, noDependenceVars, constraints);
        if (constraints.size() > 0) {
            List<Formula> constraintsList = new ArrayList<Formula>();
            constraintsList.addAll(constraints);
            AndFormula arrayIteConstraints = AndFormula
                    .generate(constraintsList);
            formula = ImpliesFormula.create(arrayIteConstraints, formula);
            storeConstraints(constraints, noDependenceVars);
            constraints.clear();
        }
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");

        // Util.writeFormulaToFile(formula, "afterRemoveArrayITE.smt2", false,
        // false); // DEBUG

        Util.printToSystemOutWithWallClockTimePrefix("  Making array reads simple...");
        timer.reset();
        timer.start();
        formula = formula.makeArrayReadsSimple(formula, constraints,
                noDependenceVars);
        if (constraints.size() > 0) {
            List<Formula> constraintsList = new ArrayList<Formula>();
            constraintsList.addAll(constraints);
            AndFormula arrayReadConstraints = AndFormula
                    .generate(constraintsList);
            formula = ImpliesFormula.create(arrayReadConstraints, formula);
            storeConstraints(constraints, noDependenceVars);
            constraints.clear();
        }
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");

        // Util.writeFormulaToFile(formula, "afterMakeReadsSimple.smt2", false,
        // false); // DEBUG

        Util.printToSystemOutWithWallClockTimePrefix("  Removing array writes...");
        timer.reset();
        timer.start();
        formula = formula.removeArrayWrites(formula, constraints,
                noDependenceVars);
        if (constraints.size() > 0) {
            List<Formula> constraintsList = new ArrayList<Formula>();
            constraintsList.addAll(constraints);
            AndFormula arrayWriteConstraints = AndFormula
                    .generate(constraintsList);
            formula = ImpliesFormula.create(arrayWriteConstraints, formula);
            storeConstraints(constraints, noDependenceVars);
            constraints.clear();
        }
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");

        // Util.writeFormulaToFile(formula, "afterRemoveArrayWrites.smt2",
        // false,
        // false); // DEBUG

        Suraq.extTimer.stopReset("after removin array reads + writes");

        Util.printToSystemOutWithWallClockTimePrefix("  Removing array equalities...");
        timer.reset();
        timer.start();
        formula = formula.removeArrayEqualities();
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");

        // Util.writeFormulaToFile(formula, "afterRemoveArrayEq.smt2", false,
        // false); // DEBUG

        Suraq.extTimer.stopReset("after removing array equalities");

        Set<DomainTerm> indexSet = formula.getIndexSet();

        lambda = DomainVariable.create(Util.freshVarNameCached(formula,
                "lambda"));

        List<Formula> lambdaDisequalities = new ArrayList<Formula>();
        for (DomainTerm index : indexSet) {
            List<DomainTerm> domainTerms = new ArrayList<DomainTerm>(2);
            domainTerms.add(lambda);
            domainTerms.add(index);
            lambdaDisequalities.add(DomainEq.create(domainTerms, false));
        }
        Formula lambdaConstraints = AndFormula.generate(lambdaDisequalities);
        indexSet.add(lambda);
        noDependenceVars.add(Token.generate(lambda.getVarName()));

        Util.printToSystemOutWithWallClockTimePrefix("  Converting array properties to finite conjunctions...");
        timer.reset();
        timer.start();
        formula = formula.arrayPropertiesToFiniteConjunctions(indexSet);
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");

        formula = ImpliesFormula.create(lambdaConstraints, formula);

        // Util.writeFormulaToFile(formula, "aftertoArrayProp.smt2", false,
        // false); // DEBUG

        Set<Token> currentDependenceArrayVariables = new HashSet<Token>();
        Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();
        formula.getArrayVariables(arrayVars, new HashSet<SMTLibObject>());
        for (ArrayVariable var : arrayVars)
            if (!noDependenceVars.contains(Token.generate(var.getVarName())))
                currentDependenceArrayVariables.add(Token.generate(var
                        .getVarName()));
        Util.printToSystemOutWithWallClockTimePrefix("  Converting array reads to uninterpreted function calls...");
        timer.reset();
        timer.start();
        formula = formula.arrayReadsToUninterpretedFunctions(noDependenceVars);
        noDependenceVars.removeAll(currentDependenceArrayVariables);
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");

        // Util.writeFormulaToFile(formula, "afterArrayToUF.smt2", false, true);
        // // DEBUG
        Suraq.extTimer.stopReset("after Array Reads to UF");

        // /////////////////////////////////////////////////
        // Perform Ackermann
        // /////////////////////////////////////////////////
        Util.printToSystemOutWithWallClockTimePrefix("  Perform Ackermann's Reduction...");
        timer.reset();
        timer.start();
        Ackermann ackermann = new Ackermann();
        formula = ackermann.performAckermann(formula, noDependenceVars);
        timer.end();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");
        // DebugHelper.getInstance().formulaToFile(formula,
        // "./debug_ackermann.txt");
        Suraq.extTimer.stopReset("after Ackermann");

        // /////////////////////////////////////////////////

        // Reduction of var1 = ITE(cond, var2, var3)
        // to var1 = itevar & ITE(cond, itevar=var2, itevar=var3)
        Util.printToSystemOutWithWallClockTimePrefix("  Perform ITE Reduction...");
        timer.reset();
        timer.start();
        ITEEquationReduction itered = new ITEEquationReduction();
        formula = itered.perform(formula, noDependenceVars);
        storeConstraints(itered.getConstraints(), noDependenceVars);
        timer.end();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");
        // DebugHelper.getInstance().formulaToFile(formula, "./debug_ite.txt");
        Suraq.extTimer.stopReset("after ITE equality trans");

        // /////////////////////////////////////////////////
        // Perform Graph Based Reduction
        // /////////////////////////////////////////////////
        Util.printToSystemOutWithWallClockTimePrefix("  Perform Graph-Based Reduction...");
        timer.reset();
        timer.start();
        GraphReduction graphReduction = new GraphReduction();
        try {
            formula = graphReduction.perform(formula, noDependenceVars);
        } catch (Exception ex) {
            ex.printStackTrace();
        }
        timer.end();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");
        Suraq.extTimer.stopReset("after Graph reduction");

        // /////////////////////////////////////////////////
        // DebugHelper.getInstance().formulaToFile(formula,
        // "./debug_graph.txt");

        List<PropositionalVariable> controlSignals = logicParser
                .getControlVariables();

        // /////////////////////////////////////////////////
        // TSEITIN-Encoding + QBF Encoding
        // /////////////////////////////////////////////////
        boolean qbfsolver = QBFEncoder.isActive();
        if (qbfsolver) {
            // debug:
            // formula = NotFormula.create(formula);

            TseitinEncoding tseitin = new TseitinEncoding();
            formula = tseitin.performTseitinEncodingWithoutZ3(formula);
            DebugHelper.getInstance().formulaToFile(formula,
                    "./debug_tseitin.txt");

            QBFEncoder qbfEncoder = new QBFEncoder();
            String qbf = qbfEncoder.encode(formula, noDependenceVars,
                    controlSignals, tseitin.getPropositionalVariables());
            DebugHelper.getInstance().stringtoFile(qbf, "./debug_qbf.txt");

            QBFSolver qbfSolver = new QBFSolver();
            qbfSolver.solve(qbf);
            // int state = qbfSolver.getState();
            // if(state == QBFSolver.SAT)
            System.err
                    .println("System.exit(0) in Suraq.java(2104) because of QBF.");
            Suraq.extTimer.stopReset("after QBF enc");
            System.exit(0);
            return null;
        }

        System.err.println(Suraq.extTimer);
        return formula;
    }

    /**
     * Expands the given formula for the given <code>controlSignals</code> and
     * the nodepvars in the field <code>noDependenceVars</code>.
     * 
     * Initializes the fields <code>declarationStr</code> and
     * <code>outputExpressions</code>.
     * 
     * @param formula
     * @param controlSignals
     * @throws SuraqException
     */
    private void prepareOutputExpressions(Formula formula,
            List<PropositionalVariable> controlSignals) throws SuraqException {
        Timer timer = new Timer();

        Util.printToSystemOutWithWallClockTimePrefix("  Writing declarations...");

        timer.reset();
        timer.start();
        writeDeclarationsAndDefinitions(formula, noDependenceVars,
                controlSignals.size());
        timer.stop();
        Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                + ")");

        writeAssertPartitions(formula, noDependenceVars, controlSignals);

        Suraq.extTimer.stopReset("</doMainWork>");

    }

    /**
     * Performs the main work.
     * 
     * @return
     * 
     * @throws SuraqException
     *             if something goes wrong
     */
    private Formula doMainWork() throws SuraqException {
        Formula formula = performFormulaReductions();
        List<PropositionalVariable> controlSignals = logicParser
                .getControlVariables();
        if (controlSignals.size() > 30) {
            throw new SuraqException(
                    "Current implementation cannot handle more than 30 control signals.");
        }
        prepareOutputExpressions(formula, logicParser.getControlVariables());
        return formula;
    }

    /**
     * Stores all equality constraints in the given set to the
     * <code>constraints</code> field. Ignores non-equality formulas (i.e.,
     * array properties). Also ignores constraints that contain
     * noDependenceVars.
     * 
     * @param currentConstraints
     * @param noDependenceVars
     */
    private void storeConstraints(Collection<Formula> currentConstraints,
            Set<Token> noDependenceVars) {
        for (Formula constraint : currentConstraints) {
            if (!Util.formulaContainsAny(constraint, noDependenceVars))
                this.constraints.add(constraint);
        }
    }

    /**
     * Writes the assert-partitions for the expanded formula to the
     * <code>outputExpressions</code>.
     * 
     * @param formula
     *            the main formula to expand
     * @param noDependenceVars
     *            the variables (and functions) on which the controller may not
     *            depend
     * @param controlSignals
     *            the control signals
     * @throws SuraqException
     *             if something goes wrong
     */
    private void writeAssertPartitions(Formula formula,
            Set<Token> noDependenceVars,
            List<PropositionalVariable> controlSignals) throws SuraqException {

        // if (outputExpressions == null)
        // throw new SuraqException("outputExpressions not initialized!");

        for (int count = 0; count < (1 << controlSignals.size()); count++) {
            Util.printToSystemOutWithWallClockTimePrefix("  Writing assert-partition number "
                    + (count + 1) + " of " + (1 << controlSignals.size()));
            Formula tempFormula = formula;// .deepFormulaCopy();
            Map<Token, Term> variableSubstitutions = new HashMap<Token, Term>();
            Map<Token, UninterpretedFunction> ufSubstitutions = new HashMap<Token, UninterpretedFunction>();

            // Debug counters for progress statistics:
            Util.printToSystemOutWithWallClockTimePrefix("There are "
                    + noDependenceVars.size() + " nodepvars");
            // int varCount = 0;
            // int lastPrint = 0;

            for (Token var : noDependenceVars) {
                // if (varCount++ >= (int) Math.ceil(lastPrint
                // * ((double) noDependenceVars.size() / 100))) {
                // System.out.print((++lastPrint) + "% ");
                // }
                // if (lastPrint == 100 || varCount == noDependenceVars.size())
                // System.out.println();
                if (noDependenceVarsCopies.containsKey(var))
                    // it's a variable
                    variableSubstitutions.put(var,
                            noDependenceVarsCopies.get(var).get(count));
                else if (noDependenceFunctionsCopies.containsKey(var)) {
                    // it's an uninterpreted function
                    // System.err.println("There was a function (Ackerman didn't perform?)");

                    // old and slow:
                    // tempFormula =
                    // tempFormula.substituteUninterpretedFunction(var,
                    // noDependenceFunctionsCopies.get(var).get(count));

                    // new (chillebold):
                    ufSubstitutions.put(var,
                            noDependenceFunctionsCopies.get(var).get(count));
                } else
                    // Util.printToSystemOutWithWallClockTimePrefix(
                    // " This could be an exception: "+
                    throw new SuraqException(
                            "noDependenceVar "
                                    + var.toString()
                                    + " is neither a variable nor an uninterpreted function.");
            }

            tempFormula = tempFormula.substituteUninterpretedFunction(
                    ufSubstitutions, new HashMap<SMTLibObject, SMTLibObject>());

            int currentCount = count;
            int mask = 1;
            for (int signalCount = 0; signalCount < controlSignals.size(); signalCount++) {
                variableSubstitutions.put(Token.generate(controlSignals.get(
                        signalCount).getVarName()), PropositionalConstant
                        .create((currentCount & mask) != 0));
                currentCount = currentCount >> 1;
            }

            tempFormula = tempFormula.substituteFormula(variableSubstitutions,
                    new HashMap<SMTLibObject, SMTLibObject>());
            tempFormula = NotFormula.create(tempFormula);
            this.assertPartitionFormulas.put(count + 1, tempFormula);
            // SExpression assertPartitionExpression = new SExpression();
            // assertPartitionExpression.addChild(SExpressionConstants.ASSERT);
            // // .addChild(SExpressionConstants.ASSERT_PARTITION);
            // assertPartitionExpression.addChild(tempFormula.toSmtlibV2());
            // outputExpressions.add(assertPartitionExpression);
        }
    }

    /**
     * Writes the declarations of all domain variables, propositional variables,
     * uninterpreted functions, as well as the definition of all macros in
     * <code>formula</code>. For <code>noDependenceVars</code>, 2^
     * <code>numControlSignals</code> copies are declared.
     * 
     * @param formula
     *            The formula for which to write the definitions.
     * @param noDependenceVars
     *            the set of variables on which the controller may not depend.
     * @param numControlSignals
     *            the number of control signals.
     * @throws SuraqException
     *             if something goes wrong.
     */
    private void writeDeclarationsAndDefinitions(Formula formula,
            Set<Token> noDependenceVars, int numControlSignals)
            throws SuraqException {

        Util.printToSystemOutWithWallClockTimePrefix("   step 0");

        varTypes = new HashMap<Token, SExpression>();
        varTypes.put(Token.generate(lambda.getVarName()),
                SExpressionConstants.VALUE_TYPE);
        Map<Token, Integer> functionArity = new HashMap<Token, Integer>();

        Set<PropositionalVariable> pVars = new HashSet<PropositionalVariable>();
        Set<SMTLibObject> done = new HashSet<SMTLibObject>();
        formula.getPropositionalVariables(pVars, done);
        done.clear();
        Util.printToSystemOutWithWallClockTimePrefix("   step 1: prop. vars: "
                + pVars.size());
        for (PropositionalVariable var : pVars) {
            if (noDependenceVars.contains(var.toSmtlibV2())) {
                varTypes.put(Token.generate(var.getVarName()),
                        SExpressionConstants.BOOL_TYPE);
                continue; // noDependenceVars will be handled later.
            }
            // outputExpressions
            // .add(SExpression.makeDeclareFun((Token) var.toSmtlibV2(),
            // SExpressionConstants.BOOL_TYPE, 0));
        }

        Set<DomainVariable> dVars = new HashSet<DomainVariable>();
        formula.getDomainVariables(dVars, done);
        done.clear();
        Util.printToSystemOutWithWallClockTimePrefix("   step 2: domain vars: "
                + dVars.size());
        for (DomainVariable var : dVars) {
            if (noDependenceVars.contains(var.toSmtlibV2())) {
                varTypes.put(Token.generate(var.getVarName()),
                        SExpressionConstants.VALUE_TYPE);
                continue; // noDependenceVars will be handled later.
            }
            // outputExpressions.add(SExpression.makeDeclareFun(
            // (Token) var.toSmtlibV2(), SExpressionConstants.VALUE_TYPE,
            // 0));
        }

        Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();
        formula.getArrayVariables(arrayVars, done);
        done.clear();
        Util.printToSystemOutWithWallClockTimePrefix("   step 3: debug / Array Vars: "
                + arrayVars.size());
        // DEBUG
        // For debugging purposes, also handle array variables
        // (so that performing only some of the reductions can be tested)
        for (ArrayVariable var : arrayVars) {
            if (noDependenceVars.contains(var.toSmtlibV2())) {
                varTypes.put(Token.generate(var.getVarName()),
                        SExpressionConstants.ARRAY_TYPE);
                continue; // noDependenceVars will be handled later.
            }
            // outputExpressions.add(SExpression.makeDeclareFun(
            // (Token) var.toSmtlibV2(), SExpressionConstants.ARRAY_TYPE,
            // 0));
        } // end debug

        Set<UninterpretedFunction> ufs = new HashSet<UninterpretedFunction>();
        formula.getUninterpretedFunctions(ufs, done);
        done.clear();
        Util.printToSystemOutWithWallClockTimePrefix("   step 4: UF: "
                + ufs.size());
        for (UninterpretedFunction function : ufs) {
            if (noDependenceVars.contains(function.getName())) {
                varTypes.put(Token.generate(function.getName()),
                        SExpressionConstants.VALUE_TYPE);
                functionArity.put(function.getName(), function.getNumParams());
                continue; // noDependenceVars will be handled later.
            }
            // outputExpressions.add(SExpression.makeDeclareFun(
            // function.getName(), function.getType(),
            // function.getNumParams()));
        }

        long _cnt = noDependenceVars.size();
        long stepsize = _cnt / 100 + 1;
        Util.printToSystemOutWithWallClockTimePrefix("   step 5: no dep vars: there are #"
                + _cnt + "; numControlSignals=" + numControlSignals);
        // Now dealing with noDependenceVars
        noDependenceVarsCopies = new HashMap<Token, List<Term>>();
        noDependenceFunctionsCopies = new HashMap<Token, List<UninterpretedFunction>>();
        long cnt = 0;
        int numCopies = (1 << numControlSignals);

        // info: Performance improved by factor #noDependenceVars

        for (Token var : noDependenceVars) {

            // debug output:
            if (cnt++ % stepsize == 0)
                System.out.print((100 * cnt) / _cnt + "% ");

            SExpression type = varTypes.get(var);
            if (type == null) {
                System.err
                        .println("Type is null for '" + var + "'. Strange...");
            }
            assert (type != null);
            int numParams = 0;
            if (functionArity.containsKey(var))
                numParams = functionArity.get(var);

            List<Term> listOfVarCopies = null;
            if (noDependenceVarsCopies.containsKey(var))
                listOfVarCopies = noDependenceVarsCopies.get(var);
            if (listOfVarCopies == null)
                listOfVarCopies = new ArrayList<Term>();
            if (numParams == 0)
                noDependenceVarsCopies.put(var, listOfVarCopies);

            List<UninterpretedFunction> listOfFunctionCopies = null;
            if (noDependenceFunctionsCopies.containsKey(var))
                listOfFunctionCopies = noDependenceFunctionsCopies.get(var);
            if (listOfFunctionCopies == null)
                listOfFunctionCopies = new ArrayList<UninterpretedFunction>();
            if (numParams > 0)
                noDependenceFunctionsCopies.put(var, listOfFunctionCopies);

            for (int count = 1; count <= numCopies; count++) {

                String name = Util.freshVarNameCached(formula, var.toString()
                        + "_copy_" + count);
                // outputExpressions.add(SExpression.makeDeclareFun(
                // Token.generate(name), type, numParams));
                if (numParams == 0) {
                    if (type.equals(SExpressionConstants.BOOL_TYPE))
                        listOfVarCopies.add(PropositionalVariable.create(name,
                                count));
                    else if (type.equals(SExpressionConstants.VALUE_TYPE))
                        listOfVarCopies.add(DomainVariable.create(name, count));
                    else {
                        assert (type.equals(SExpressionConstants.ARRAY_TYPE));
                        listOfVarCopies.add(ArrayVariable.create(name, count));
                    }
                } else {
                    assert (type instanceof Token);
                    listOfFunctionCopies.add(UninterpretedFunction.create(name,
                            numParams, (Token) type, count));
                }
            }
        }
        Util.printToSystemOutWithWallClockTimePrefix("\n   step 6: macro");
        Set<FunctionMacro> macros = new HashSet<FunctionMacro>();
        formula.getFunctionMacros(macros, done);
        done.clear();
        // for (FunctionMacro macro : macros)
        // outputExpressions.add(macro.toSmtlibV2());
    }

    /**
     * Prints a final message.
     * 
     * @param result
     *            <code>true</code> if there were no errors, <code>false</code>
     *            otherwise.
     * @param overallTimer
     */
    private void printEnd(boolean result, Timer overallTimer) {
        System.out
                .println("################################################################################");
        Util.printToSystemOutWithWallClockTimePrefix("  (Overall time - excluding checking of results: "
                + overallTimer + ")");
        if (result)

            if (SuraqOptions.getInstance().isCheckResult())
                Util.printToSystemOutWithWallClockTimePrefix("LIVE LONG AND PROSPER!");
            else
                Util.printToSystemOutWithWallClockTimePrefix("Live long and prosper!");
        else
            Util.printToSystemOutWithWallClockTimePrefix("There were errors.\nRESISTANCE IS FUTILE!");
    }

    /**
     * 
     */
    private void printWelcome() {
        System.out
                .println("################################################################################");
        System.out.println("                                  Welcome to");
        System.out
                .println("              _____   __    __   ______       ____       ____");
        System.out
                .println("             / ____\\  ) )  ( (  (   __ \\     (    )     / __ \\");
        System.out
                .println("            ( (___   ( (    ) )  ) (__) )    / /\\ \\    / /  \\ \\");
        System.out
                .println("             \\___ \\   ) )  ( (  (    __/    ( (__) )  ( (    ) )");
        System.out
                .println("                 ) ) ( (    ) )  ) \\ \\  _    )    (   ( (  /\\) )");
        System.out
                .println("             ___/ /   ) \\__/ (  ( ( \\ \\_))  /  /\\  \\   \\ \\_\\ \\/");
        System.out
                .println("            /____/    \\______/   )_) \\__/  /__(  )__\\   \\___\\ \\_");
        System.out
                .println("                                                             \\__)");
        System.out.println("                                         MMM.");
        System.out.println("                          NM.           MMMMM");
        System.out.println("                         MMMM?         IMMMMM MMM");
        System.out.println("                         MMMMN         MMMMMM MMM");
        System.out
                .println("                         MMMMO        MMMMMMM?MMMD");
        System.out
                .println("                         MMMMM        MMMMMM MMMMM");
        System.out
                .println("                      .M MMMMM       OMMMMMM MMMMO");
        System.out.println("                     MMMM$MMMM       MMMMMM 7MMMM");
        System.out.println("                     MMMMNMMMM       MMMMMM MMMMM");
        System.out.println("                     MMMMMMMMM      MMMMMM.,MMMMM");
        System.out.println("                     MMMMMZMMMM     MMMMMM MMMMM");
        System.out.println("                     MMMMM MMMM     MMMMMM MMMMM");
        System.out.println("                     MMMMM MMMMM    MMMMM MMMMMM");
        System.out.println("                     MMMMM DMMMM   MMMMMM MMMMM");
        System.out.println("                     MMMMM .MMMMMMMMMMMMM7MMMMM");
        System.out.println("                     MMMMMM MMMMMMMMMMMMMMMMMMM");
        System.out.println("                     MMMMMMMMMMMMMMMMMMMMMMMMMM");
        System.out.println("                     =MMMMMMMMMMMMMMMMMMMMMMMMM");
        System.out.println("                      MMMMMMMMMMMMMMMMMMMMMMMMD");
        System.out.println("                     MMMMMMMMMMMMMMMMMMMMMMMMMM");
        System.out
                .println("                     MMMMMMMMMMMMMMMMMMMMMMMMMM            MMMMMMMM");
        System.out
                .println("                     MMMMMMMMMMMMMMMMMMMMMMMMMMM       =MMMMMMMMMMM");
        System.out
                .println("                     MMMMMMMMMMMMMMMMMMMMMMMMMMMM7 IMMMMMMMMMMMMMM");
        System.out
                .println("                     MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM");
        System.out
                .println("                     MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM");
        System.out
                .println("                     MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM");
        System.out
                .println("                     MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMO");
        System.out
                .println("                      MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM");
        System.out
                .println("                      MMMMMMMMMMMMMMMMMMMMMMMMMMMMM");
        System.out.println("                      MMMMMMMMMMMMMMMMMMMMMMMMM");
        System.out.println("                        MMMMMMMMMMMMMMMMMMMM");
        System.out.println("                            =MMMMMMMMMMMMM");
        System.out.println("                                  MMMM,");
        System.out.println("");
        System.out
                .println("################################################################################");
        System.out.println("");
    }

    /**
     * Parses a Z3 proof string.
     * 
     * @param proofStr
     *            the string to parse.
     * @param propositionalVars
     *            list of propositional variables.
     * @param domainVars
     *            list of domain variables.
     * @param arrayVars
     *            list of array variables.
     * @param uninterpretedFunctions
     *            list of uninterpreted functions.
     * @return the Z3Proof Object
     * 
     */
    @Deprecated
    @SuppressWarnings("unused")
    private Z3Proof parseProof(String proofStr,
            Set<PropositionalVariable> propsitionalVars,
            Set<DomainVariable> domainVars, Set<ArrayVariable> arrayVars,
            Set<UninterpretedFunction> uninterpretedFunctions) {
        // expression parsing of proof
        SExpParser sExpProofParser = null;
        sExpProofParser = new SExpParser(proofStr);

        Timer timer = new Timer();

        try {
            Util.printToSystemOutWithWallClockTimePrefix("  Parsing proof to S-Expressions...");
            timer.start();
            sExpProofParser.parse();
            assert (sExpProofParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            noErrors = false;
        } finally {
            timer.stop();
            Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                    + ")");
            timer.reset();
        }

        // parsing proof
        Set<PropositionalVariable> allPropVars = new HashSet<PropositionalVariable>();
        allPropVars.addAll(propsitionalVars);
        allPropVars.addAll(tseitinEncoding.keySet());
        ProofParser proofParser = new ProofParser(
                sExpProofParser.getRootExpr(), domainVars, allPropVars,
                arrayVars, uninterpretedFunctions);

        try {
            Util.printToSystemOutWithWallClockTimePrefix("  Parsing proof to SMTLIB objects...");
            timer.start();
            proofParser.parse();
            assert (proofParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            exc.printStackTrace();
            handleParseError(exc);
            noErrors = false;
            throw new RuntimeException("Unable to parse proof!");
        } finally {
            timer.stop();
            Util.printToSystemOutWithWallClockTimePrefix("    Done. (" + timer
                    + ")");
            timer.reset();
        }

        return proofParser.getRootProof();
    }

    /**
     * Prints error message of a parse error.
     * 
     * @param exc
     *            the parse error.
     */
    private void handleParseError(ParseError exc) {
        exc.printStackTrace();
        System.err.println("PARSE ERROR!");
        System.err.println(exc.getMessage());
        System.err.println("Line: "
                + (exc.getLineNumber() > 0 ? exc.getLineNumber() : "unknown"));
        System.err.println("Column: "
                + (exc.getColumnNumber() > 0 ? exc.getColumnNumber()
                        : "unknown"));
        System.err
                .println("Context: "
                        + (exc.getContext() != "" ? exc.getContext()
                                : "not available"));
    }

    /**
     * Prints size information of the given proof.
     * 
     * @param proof
     */
    private void printProofStats(Z3Proof proof) {

        SuraqOptions options = SuraqOptions.getInstance();

        if (options.isVerbose()) {
            DecimalFormat myFormatter = new DecimalFormat("###,###,###");
            Timer dagTimer = new Timer();
            dagTimer.start();
            int dagSize = proof.size(false);
            dagTimer.stop();
            String dagSizeString = myFormatter.format(dagSize);
            Util.printToSystemOutWithWallClockTimePrefix("    Proof (DAG)  size: "
                    + dagSizeString + " (computed in " + dagTimer + ")");
            Timer treeTimer = new Timer();
            treeTimer.start();
            int treeSize = proof.size(true);
            treeTimer.stop();
            String treeSizeString = myFormatter.format(treeSize);
            Util.printToSystemOutWithWallClockTimePrefix("    Proof (tree) size: "
                    + treeSizeString + " (computed in " + treeTimer + ")");

            Timer depthTimer = new Timer();
            depthTimer.start();
            int depth = proof.depth();
            depthTimer.stop();
            Util.printToSystemOutWithWallClockTimePrefix("    Proof depth: "
                    + depth + " (computed in " + depthTimer + ")");
            System.out.println();
            System.out.println();
        }
    }

    /**
     * Dump the assertPartitionFormulas (and the required declarations) to the
     * given <code>filename</code>. Some extra information will be prepended.
     * 
     * @param query
     * @param filename
     */
    private void dumpSMTQuery(String filename) {
        try {
            Util.printToSystemOutWithWallClockTimePrefix("Dumping SMT query to file "
                    + filename);
            File file = new File(filename);
            FileWriter fw = new FileWriter(file);
            BufferedWriter writer = new BufferedWriter(fw);
            writer.write("; This SMT file was created by the SURAQ synthesis tool.\n");
            writer.write("; Date and time of creation: ");
            writer.write(new SimpleDateFormat("yyyy-MM-dd HH:mm")
                    .format(Calendar.getInstance().getTime()));
            writer.write("\n");
            writer.write("; Original spec file: ");
            writer.write(SuraqOptions.getInstance().getInput());
            writer.write("\n");
            writer.write("; Expected result: UNSAT\n;\n");
            writer.write("; For more information contact Georg Hofferek <georg.hofferek@iaik.tugraz.at>.\n\n");

            writer.write(SExpressionConstants.SET_LOGIC_QF_UF.toString());
            writer.write(SExpressionConstants.DECLARE_SORT_VALUE.toString());
            // writer.write(declarationStr);
            Util.writeDeclarations(AndFormula.generate(new ArrayList<Formula>(
                    assertPartitionFormulas.values())), writer);
            writer.write("\n");
            int count = 0;
            for (Integer key : assertPartitionFormulas.keySet()) {
                Util.printToSystemOutWithWallClockTimePrefix("Dumping partition "
                        + ++count + " of " + assertPartitionFormulas.size());
                Formula partitionFormula = assertPartitionFormulas.get(key);
                writer.write("(assert ");
                writer.write(partitionFormula.toString());
                writer.write(")\n");
            }
            writer.write(SExpressionConstants.CHECK_SAT.toString());
            writer.close();
        } catch (IOException exc) {
            Util.printToSystemOutWithWallClockTimePrefix("ERROR: IOException occured while dumping SMT query. Dump may be incomplete.");
        }
        if (SuraqOptions.getInstance().getExitAfterDump()) {
            Util.printToSystemOutWithWallClockTimePrefix("Done dumping. Will exit now because exitAfterDump was specified.");
            System.exit(0);
        }
    }

    /**
     * This method is for use in debugging; <strong>DO NOT USE IN
     * PRODUCTION!</strong> It will just do all input transformations (to create
     * internal data structure about the formula), and then parse the veriT
     * proof given by <code>proofReader</code>. It will return the parsed
     * <code>VeritProof</code>.
     * 
     * @param proofReader
     *            to read the proof from
     * @return parsed proof
     */
    public VeritProof justDoInputTransformationAndThenParseThisProofFile(
            BufferedReader proofReader) {
        inputTransformations(new File(SuraqOptions.getInstance().getInput()));

        VeriTParser parser = new VeriTParser(proofReader, mainFormula,
                tseitinEncoding.keySet(), noDependenceVarsCopies.values(),
                noDependenceFunctionsCopies);

        parser.parse();
        return parser.getProof();
    }
}
