/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.main;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.parser.LogicParser;
import at.iaik.suraq.parser.ProofParser;
import at.iaik.suraq.parser.SExpParser;
import at.iaik.suraq.parser.TseitinParser;
import at.iaik.suraq.resProof.ResProof;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.TransformedZ3Proof;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.FunctionMacro;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtsolver.SMTSolver;
import at.iaik.suraq.util.SaveCache;
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

    /**
     * The expressions that will be written to the output.
     */
    private List<SExpression> outputExpressions;

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
    private Set<PropositionalVariable> propsitionalVars;
    /**
     * stores all present domain variables
     */
    private Set<DomainVariable> domainVars;
    /**
     * stores all present array variables
     */
    private Set<ArrayVariable> arrayVars;
    /**
     * stores all present uninterpreted functions
     */
    private Set<UninterpretedFunction> uninterpretedFunctions;

    /**
     * stores the assert partition formula for each assert partition
     */
    private Map<Integer, Formula> assertPartitionFormulas = new HashMap<Integer, Formula>();

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
            Suraq suraq = new Suraq(args);
            suraq.run();

        } catch (Throwable exc) {
            System.err.println("ERROR: Uncaught exception!");
            exc.printStackTrace();
            System.exit(-1);
        }
        System.exit(0);
    }

    private String inputTransformations(File sourceFile) {

        SuraqOptions options = SuraqOptions.getInstance();

        SExpParser sExpParser = null;
        try {
            sExpParser = new SExpParser(sourceFile);
        } catch (FileNotFoundException exc) {
            System.err.println("ERROR: File " + sourceFile.getPath()
                    + " not found!");
            noErrors = false;
            return null;
        } catch (IOException exc) {
            System.err.println("ERROR: Could not read from file "
                    + sourceFile.getPath());
            noErrors = false;
            return null;
        }

        Timer sExpParseTimer = new Timer();
        sExpParseTimer.start();
        try {
            sExpParser.parse();
            assert (sExpParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            noErrors = false;
            return null;
        } finally {
            sExpParseTimer.end();
            System.out.println("S-Expression parsing took " + sExpParseTimer);
        }

        logicParser = new LogicParser(sExpParser.getRootExpr());

        Timer logicParseTimer = new Timer();
        try {
            logicParseTimer.start();
            logicParser.parse();
            assert (logicParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            noErrors = false;
            return null;
        } finally {
            logicParseTimer.end();
            System.out.println("Logic parsing took " + logicParseTimer);
        }
        // Parsing complete
        if (options.isVerbose())
            System.out.println("Parsing completed successfully!");

        try {
            mainFormula = doMainWork();
        } catch (SuraqException exc) {
            noErrors = false;
            if (exc.getMessage() != null)
                System.out.println(exc.getMessage());
        }

        // build function and variable lists for parser
        propsitionalVars = mainFormula.getPropositionalVariables();
        domainVars = mainFormula.getDomainVariables();
        arrayVars = mainFormula.getArrayVariables();
        uninterpretedFunctions = mainFormula.getUninterpretedFunctions();

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
                    propsitionalVars.add((PropositionalVariable) var);

            if (first instanceof ArrayVariable)
                for (Term var : varList.getValue())
                    arrayVars.add((ArrayVariable) var);
        }

        for (Map.Entry<Token, List<UninterpretedFunction>> functionList : noDependenceFunctionsCopies
                .entrySet())
            uninterpretedFunctions.addAll(functionList.getValue());

        System.out
                .println("  Simplifying assert-partitions and tseitin-cnf encoding...");

        Timer allPartitionsTimer = new Timer();
        allPartitionsTimer.start();

        List<String> tseitinPartitions = new ArrayList<String>();

        if (options.getTseitinType() == options.TSEITIN_WITHOUT_Z3) {
            System.out.println("  Performing tseitin encoding without Z3...");
            tseitinPartitions = performTseitinEncodingWithoutZ3();
        } else {
            System.out.println("  Performing tseitin encoding with Z3...");
            tseitinPartitions = performTseitinEncodingWithZ3();
        }

        allPartitionsTimer.end();
        System.out.println("  All partitions done. (" + allPartitionsTimer
                + ")");

        String z3InputStr = buildSMTDescriptionFromTseitinPartitions(
                declarationStr, tseitinPartitions);

        return z3InputStr;
    }

    private List<String> performTseitinEncodingWithZ3() {

        int count = 1;
        Timer onePartitionTimer = new Timer();
        SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type,
                SuraqOptions.getZ3_4Path());

        List<String> tseitinPartitions = new ArrayList<String>();

        for (SExpression assertPartition : assertPartitionList) {

            onePartitionTimer.reset();
            onePartitionTimer.start();
            System.out.println("    Encoding partition " + count + "...");

            String smtStr = buildSMTDescriptionForTseitinEncoding(
                    declarationStr, assertPartition.toString());
            String tseitingStr = z3.tseitin_encode(smtStr);

            TseitinParser parser = parseTseitinStr(tseitingStr, count);
            Formula partitionFormula = parser.getRootFormula();

            tseitinPartitions.add(partitionFormula.toString());

            System.out.println("      test if tseitin encoding is correct...");
            assert (TseitinParser.checkFormulaImplication(partitionFormula,
                    assertPartitionFormulas.get(count)));
            System.out.println("      ...test finished");

            onePartitionTimer.end();
            System.out.println(" Done. (" + onePartitionTimer + ")");
            count++;

        }
        return tseitinPartitions;
    }

    private List<String> performTseitinEncodingWithoutZ3() {

        Timer onePartitionTimer = new Timer();
        List<String> tseitinPartitions = new ArrayList<String>();

        for (int count = 1; count <= assertPartitionFormulas.size(); count++) {
            onePartitionTimer.reset();
            onePartitionTimer.start();
            System.out.println("    Encoding partition " + count + "...");

            Formula partitionFormula = assertPartitionFormulas.get(count);

            List<OrFormula> clauses = new ArrayList<OrFormula>();
            Map<PropositionalVariable, Formula> encoding = new HashMap<PropositionalVariable, Formula>();
            PropositionalVariable tseitinVar = partitionFormula.tseitinEncode(
                    clauses, encoding);
            tseitinEncoding.putAll(encoding);
            tseitinEncoding.put(tseitinVar, partitionFormula);

            List<Formula> disjuncts = new ArrayList<Formula>(1);
            disjuncts.add(tseitinVar);
            clauses.add(new OrFormula(disjuncts));
            Formula encodedPartitionFormula = new AndFormula(clauses);

            System.out.println("      test if tseitin encoding is correct...");
            assert (TseitinParser.checkFormulaImplication(partitionFormula,
                    assertPartitionFormulas.get(count)));
            System.out.println("      ...test finished");

            onePartitionTimer.end();
            System.out.println(" Done. (" + onePartitionTimer + ")");
            tseitinPartitions.add(encodedPartitionFormula.toString());

        }
        return tseitinPartitions;
    }

    private Map<PropositionalVariable, Formula> proofTransformationAndInterpolation(
            Z3Proof rootProof, SaveCache intermediateVars) {

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

        printProofSize(rootProof);

        // timer.start();
        // int all_nodes_size = rootProof.allNodes().size();
        // timer.end();
        // System.out.println("  All nodes size: " + all_nodes_size);
        // System.out.println("  (computed in " + timer + ")");

        // System.out.println("  Local lemmas to assertions...");
        // timer.start();
        // rootProof.localLemmasToAssertions();
        // timer.end();
        // System.out.println("    Done. (" + timer + ")");
        // timer.reset();
        // // assert (rootProof.checkZ3ProofNodeRecursive());
        // timer.start();
        // System.out.println("    Proof DAG size: " + rootProof.size(false));
        // timer.end();
        // System.out.println("      Size computed in " + timer);
        // timer.reset();
        // timer.start();
        // System.out.println("    Proof size after unwinding DAG: "
        // + rootProof.size(true));
        // timer.end();
        // System.out.println("      Size computed in " + timer);
        // timer.reset();
        // System.out.println();

        System.out.println("  Remove local sub-proofs...");
        timer.start();
        rootProof.removeLocalSubProofs();

        timer.end();
        System.out.println("    Done. (" + timer + ")");
        timer.reset();
        // assert (rootProof.checkZ3ProofNodeRecursive());
        printProofSize(rootProof);

        // System.out.println("Num Instances: " +
        // Z3Proof.numInstances());
        System.out.println("  Conversion to transformed z3 proof...");
        timer.start();
        TransformedZ3Proof transformedZ3Proof = TransformedZ3Proof
                .convertToTransformedZ3Proof(rootProof);
        timer.end();
        System.out.println("    Done. (" + timer + ")");
        timer.reset();
        printProofSize(transformedZ3Proof);

        /*
         * System.out.println("Num Instances: " + Z3Proof.numInstances()); try {
         * File smtfile = new File("proofTemp.txt"); FileWriter fstream = new
         * FileWriter(smtfile); BufferedWriter smtfilewriter = new
         * BufferedWriter(fstream); rootProof.resetMarks();
         * smtfilewriter.write(rootProof.prettyPrint()); smtfilewriter.close();
         * } catch (IOException exc) {
         * System.err.println("Error while writing to smtfile.");
         * exc.printStackTrace(); noErrors = false; }
         */
        // assert (transformedZ3Proof.checkZ3ProofNodeRecursive());

        System.out.println("  To local proof...");
        timer.start();
        transformedZ3Proof.toLocalProof();
        timer.end();
        System.out.println("    Done. (" + timer + ")");
        timer.reset();
        // assert (transformedZ3Proof.checkZ3ProofNodeRecursive());
        assert (transformedZ3Proof.isLocal());
        printProofSize(transformedZ3Proof);
        // System.out
        // .println("----Check:"
        // + transformedZ3Proof
        // .checkLeafsAgainstOriginalFormula(this.assertPartitionFormulas));
        System.out.println("  To resolution proof...");
        timer.start();
        transformedZ3Proof.toResolutionProof();
        timer.end();
        System.out.println("    Done. (" + timer + ")");
        timer.reset();
        printProofSize(transformedZ3Proof);
        // System.out
        // .println("----Check:"
        // + transformedZ3Proof
        // .checkLeafsAgainstOriginalFormula(this.assertPartitionFormulas));

        // START: ASHUTOSH code
        System.out.println("  To resolution proof format...");
        timer.start();
        ResProof resolutionProof = Util
                .createResolutionProof(transformedZ3Proof);
        timer.end();
        System.out.println("    Done. (" + timer + ")");
        timer.reset();

        System.out.println("  Check and transform resolution proof...");
        timer.start();
        // resolutionProof.dumpProof();
        resolutionProof.checkProof(false);
        resolutionProof.rmDoubleLits();
        resolutionProof.checkProof(false);
        resolutionProof.deLocalizeProof();
        resolutionProof.checkProof(false);
        resolutionProof.tranformResProofs();
        timer.end();
        System.out.println("    Done. (" + timer + ")");
        timer.reset();
        // END: ASHUTOSH code

        // Transform back into Z3Proof format
        System.out.println("  Recover resolution proof...");
        timer.start();
        TransformedZ3Proof recoveredProof = new TransformedZ3Proof(
                resolutionProof.getRoot(), Util.getLiteralMap());
        timer.end();
        System.out.println("    Done. (" + timer + ")");
        timer.reset();
        printProofSize(recoveredProof);
        // System.out
        // .println("----Check:"
        // + recoveredProof
        // .checkLeafsAgainstOriginalFormula(this.assertPartitionFormulas));

        // create ITE-tree for every control signal
        System.out.println("  Compute interpolants...");
        timer.start();
        Map<PropositionalVariable, Formula> iteTrees = recoveredProof
                .createITETrees(intermediateVars.getControlVars(),
                        tseitinEncoding);
        timer.end();
        System.out.println("    Done. (" + timer + ")");
        timer.reset();

        return iteTrees;
    }

    /**
     * @see java.lang.Runnable#run()
     */
    @Override
    public void run() {
        overallTimer.start();
        // START: ASHUTOSH code
        // ResProofTest pTst = new ResProofTest();
        // if (pTst.takeControl())
        // return;
        // END: ASHUTOSH code
        printWelcome();

        SuraqOptions options = SuraqOptions.getInstance();

        File sourceFile = new File(options.getInput());
        if (options.isVerbose())
            System.out.println("Parsing input file " + sourceFile.toString());

        File z3InputFile = new File(options.getZ3Input());
        File z3ProofFile = new File(options.getZ3Proof());
        File saveCacheFile = new File(options.getCacheFile());
        File saveCacheSerial = new File(options.getCacheFileSerial());

        boolean useCachedResults = false;

        if (z3InputFile.exists() && z3ProofFile.exists()
                && options.getCacheType() == SuraqOptions.CACHE_FILE
                && saveCacheFile.exists()) {

            Date inputFileDate = new Date(sourceFile.lastModified());
            Date z3InputFileDate = new Date(z3InputFile.lastModified());
            Date z3ProofFileDate = new Date(z3ProofFile.lastModified());

            if ((inputFileDate.getTime() <= z3InputFileDate.getTime())
                    && (z3InputFileDate.getTime() <= z3ProofFileDate.getTime())) {

                useCachedResults = true;
                System.out
                        .println("INFO: using FILE cached intermediate results.");
                System.out.println(z3ProofFile.toString());
            }
        }

        if (z3InputFile.exists()
                && options.getCacheType() == SuraqOptions.CACHE_SERIAL
                && saveCacheSerial.exists()) {

            Date inputFileDate = new Date(sourceFile.lastModified());
            Date z3InputFileDate = new Date(z3InputFile.lastModified());
            Date cacheFileDate = new Date(saveCacheSerial.lastModified());

            if ((inputFileDate.getTime() <= z3InputFileDate.getTime())
                    && (z3InputFileDate.getTime() <= cacheFileDate.getTime())) {

                useCachedResults = true;
                System.out
                        .println("INFO: using SERIAL cached intermediate results.");
                System.out.println(saveCacheSerial.toString());
            }
        }

        String proof = null;
        Z3Proof rootProof = null;
        SaveCache intermediateVars = null;

        if (!useCachedResults) {
            System.out.println("start input transformations");
            Timer inputTransformationTimer = new Timer();
            inputTransformationTimer.start();

            String z3InputStr = inputTransformations(sourceFile);

            inputTransformationTimer.end();
            System.out.println("finished input transformations in "
                    + inputTransformationTimer + ".\n");

            // write z3Input to file //only if not read already from file
            try {
                FileWriter fstream = new FileWriter(z3InputFile);
                fstream.write(z3InputStr);
                fstream.close();
            } catch (IOException exc) {
                System.err.println("Error while writing to z3InputFile: "
                        + options.getZ3Input());
                exc.printStackTrace();
                noErrors = false;
            }

            System.out.println("start proof calculation.");
            Timer proofcalculationTimer = new Timer();
            proofcalculationTimer.start();

            SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type,
                    SuraqOptions.getZ3Path());
            z3.solve(z3InputStr);

            switch (z3.getState()) {
            case SMTSolver.UNSAT:
                break;
            case SMTSolver.SAT:
                noErrors = false;
                throw (new RuntimeException("Z3 tells us SAT."));
            default:
                noErrors = false;
                System.out
                        .println("Z3 OUTCOME ---->  UNKNOWN! CHECK ERROR STREAM.");
                throw (new RuntimeException(
                        "Z3 tells us UNKOWN STATE. CHECK ERROR STREAM."));
            }

            proofcalculationTimer.end();
            System.out.println("finished proof calculation in "
                    + proofcalculationTimer + ".\n");

            // write z3Proof to file
            if (z3.getState() == SMTSolver.UNSAT) {

                proof = z3.getProof();

                try {

                    FileWriter fstream = new FileWriter(z3ProofFile);
                    fstream.write(z3.getProof());
                    fstream.close();
                } catch (IOException exc) {
                    System.err.println("Error while writing to z3ProofFile: "
                            + options.getZ3Proof());
                    exc.printStackTrace();
                    noErrors = false;
                }
            }

            rootProof = parseProof(proof, propsitionalVars, domainVars,
                    arrayVars, uninterpretedFunctions);

            assert (rootProof != null);

            // write intermediate variables to file, if caching is enabled
            String filename;
            if (options.getCacheType() == SuraqOptions.CACHE_FILE) {
                filename = saveCacheFile.getPath();
                intermediateVars = new SaveCache(propsitionalVars, domainVars,
                        arrayVars, uninterpretedFunctions,
                        logicParser.getControlVariables(), mainFormula,
                        assertPartitionFormulas, tseitinEncoding, null,
                        filename);
            } else if (options.getCacheType() == SuraqOptions.CACHE_SERIAL) {
                filename = saveCacheSerial.getPath();
                intermediateVars = new SaveCache(propsitionalVars, domainVars,
                        arrayVars, uninterpretedFunctions,
                        logicParser.getControlVariables(), mainFormula,
                        assertPartitionFormulas, tseitinEncoding, rootProof,
                        filename);
            } else {
                intermediateVars = new SaveCache(propsitionalVars, domainVars,
                        arrayVars, uninterpretedFunctions,
                        logicParser.getControlVariables(), mainFormula,
                        assertPartitionFormulas, tseitinEncoding, null, null);
            }

        } else { // use cached files
            try {

                if (options.getCacheType() == SuraqOptions.CACHE_FILE) {
                    // read proof from file

                    Timer loadTimer = new Timer();
                    loadTimer.start();

                    FileReader reader = new FileReader(z3ProofFile);
                    BufferedReader bufferedReader = new BufferedReader(reader);
                    StringBuilder stringBuilder = new StringBuilder();
                    String currentLine = bufferedReader.readLine();
                    String ls = System.getProperty("line.separator");
                    while (currentLine != null) {
                        stringBuilder.append(currentLine);
                        stringBuilder.append(ls);
                        currentLine = bufferedReader.readLine();
                    }
                    bufferedReader.close();
                    reader.close();

                    proof = stringBuilder.toString();

                    intermediateVars = SaveCache
                            .loadSaveCacheFromFile(saveCacheFile.getPath());

                    mainFormula = intermediateVars.getMainFormula();
                    assertPartitionFormulas = intermediateVars
                            .getAssertPartitionFormulas();
                    tseitinEncoding = intermediateVars.getTseitinEncoding();

                    rootProof = parseProof(proof,
                            intermediateVars.getPropsitionalVars(),
                            intermediateVars.getDomainVars(),
                            intermediateVars.getArrayVars(),
                            intermediateVars.getUninterpretedFunctions());
                    loadTimer.end();
                    System.out.println("Cached proof loaded and parsed in: "
                            + loadTimer);
                    assert (rootProof != null);

                } else if (options.getCacheType() == SuraqOptions.CACHE_SERIAL) {
                    Timer loadTimer = new Timer();
                    loadTimer.start();
                    intermediateVars = SaveCache
                            .loadSaveCacheFromFile(saveCacheSerial.getPath());

                    mainFormula = intermediateVars.getMainFormula();
                    assertPartitionFormulas = intermediateVars
                            .getAssertPartitionFormulas();
                    tseitinEncoding = intermediateVars.getTseitinEncoding();

                    loadTimer.end();
                    System.out.println("Serialized cache loaded in: "
                            + loadTimer);
                    rootProof = intermediateVars.getProof();

                    assert (rootProof != null);

                } else
                    throw new RuntimeException(
                            "loading from cache, but cache not enabled!!");

            } catch (IOException exc) {
                System.out.println("ERROR: Could not read cached proof!");
            }
        }

        System.out
                .println("start proof transformations and interpolation calculations.");
        Timer interpolationTimer = new Timer();
        interpolationTimer.start();

        Map<PropositionalVariable, Formula> iteTrees = proofTransformationAndInterpolation(
                rootProof, intermediateVars);

        interpolationTimer.end();
        System.out
                .println("finished proof transformations and interpolation calculations in "
                        + interpolationTimer + ".\n");

        String outputStr = CreateOutputString(sourceFile, iteTrees);

        if (options.isCheckResult()) {
            System.out.println("Starting to check results with z3...");
            Timer checkTimer = new Timer();
            checkTimer.start();
            SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type, "lib/z3/bin/z3");
            z3.solve(outputStr);

            switch (z3.getState()) {
            case SMTSolver.UNSAT:
                System.out
                        .println("SUCCESSFULLY MODEL-CHECKED RESULTS WITH Z3! :-)");
                break;
            case SMTSolver.SAT:
                noErrors = false;
                System.err
                        .println("ERROR: Z3 tells us SAT. Implementation of control signal is not correct");
                break;
            default:
                noErrors = false;
                System.out
                        .println("Z3 OUTCOME ---->  UNKNOWN! CHECK ERROR STREAM.");
            }
            checkTimer.end();
            System.out.println("Check finished in " + checkTimer);

        }

        // write output file
        try {
            System.out
                    .println(" Writing output to file " + options.getOutput());
            FileWriter fstream = new FileWriter(options.getOutput());
            fstream.write(outputStr);
            fstream.close();
        } catch (IOException exc) {
            System.err.println("Error while writing to output file: "
                    + options.getOutput());
            exc.printStackTrace();
            noErrors = false;
        }

        System.out.println(" done!");

        // All done :-)
        printEnd(noErrors);
        overallTimer.end();
        System.out.println("  (Overall time: " + overallTimer + ")");
        return;
    }

    /**
     * Forms the string which represents the final result of suraq. The
     * interpolation result for each control signal is inserted in the original
     * input file, and forms the result.
     * 
     * @param interpolationFormulas
     *            Map which contains the interpolation for each control signal
     * @return the string from the union of the input file and
     *         control-signal-interpolations.
     * 
     */
    private String CreateOutputString(File sourceFile,
            Map<PropositionalVariable, Formula> inpterpolations) {

        SExpParser sExpParser = null;
        try {
            sExpParser = new SExpParser(sourceFile);
        } catch (FileNotFoundException exc) {
            System.err.println("ERROR: File " + sourceFile.getPath()
                    + " not found!");
            noErrors = false;
            return null;
        } catch (IOException exc) {
            System.err.println("ERROR: Could not read from file "
                    + sourceFile.getPath());
            noErrors = false;
            return null;
        }

        try {
            sExpParser.parse();
            assert (sExpParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            noErrors = false;
            return null;
        }

        SExpression rootExp = sExpParser.getRootExpr();
        ArrayList<SExpression> children = new ArrayList<SExpression>(
                rootExp.getChildren());

        rootExp.replaceChild(SExpressionConstants.SET_LOGIC_QF_AUFLIA, 0);
        rootExp.addChild(SExpressionConstants.DECLARE_SORT_VALUE, 1);

        int i = 1;
        for (SExpression child : children) {

            if (child.toString().contains("declare-fun")) {

                String newChild = child.toString().replace("Control", "Bool")
                        .replace(":no_dependence", " ");
                newChild = newChild.replace("\n\n", "\n");

                rootExp.replaceChild(SExpression.fromString(newChild), i);
            }

            // negate assert formulas
            if (child.toString().contains("assert")) {

                assert (child.getChildren().size() == 2);

                SExpression assertFormula = child.getChildren().get(1);

                SExpression negatedAssertFormula = new SExpression(
                        SExpressionConstants.NOT, assertFormula);

                SExpression negatedAssert = new SExpression(
                        SExpressionConstants.ASSERT, negatedAssertFormula);

                rootExp.replaceChild(negatedAssert, i);
            }
            i++;
        }

        // add new assert formulas for each control signal
        for (Map.Entry<PropositionalVariable, Formula> entry : inpterpolations
                .entrySet()) {
            PropositionalVariable controlSignal = entry.getKey();
            Formula controlFormula = entry.getValue();

            SExpression controlAssert = SExpression.makeControlAssert(
                    controlSignal, controlFormula);

            rootExp.addChild(controlAssert);

        }

        rootExp.addChild(SExpressionConstants.CHECK_SAT);

        String rootExpStr = rootExp.toString();

        int beginIndex = rootExpStr.indexOf('(');
        int endIndex = rootExpStr.lastIndexOf(')');

        return (String) rootExpStr.subSequence(beginIndex + 1, endIndex);
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
                propsitionalVars, arrayVars, uninterpretedFunctions, partition);
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
    private String buildSMTDescriptionFromTseitinPartitions(
            String declarationStr, List<String> tseitinPartitions) {

        StringBuffer smtStr = new StringBuffer();

        smtStr.append(SExpressionConstants.SET_LOGIC_QF_UF.toString());
        smtStr.append(SExpressionConstants.AUTO_CONFIG_FALSE.toString());
        smtStr.append(SExpressionConstants.PROOF_MODE_2.toString());
        smtStr.append(SExpressionConstants.SET_OPTION_PROPAGATE_BOOLEANS_FALSE
                .toString());
        smtStr.append(SExpressionConstants.SET_OPTION_PROPAGATE_VALUES_FALSE
                .toString());
        smtStr.append(SExpressionConstants.DECLARE_SORT_VALUE.toString());

        smtStr.append(declarationStr);

        // declarations for tseitin variables
        for (PropositionalVariable var : tseitinEncoding.keySet())
            smtStr.append(SExpression.makeDeclareFun(
                    new Token(var.getVarName()),
                    SExpressionConstants.BOOL_TYPE, 0));

        for (String tseitinPartition : tseitinPartitions) {
            smtStr.append("(assert " + tseitinPartition + ")");
        }

        smtStr.append(SExpressionConstants.CHECK_SAT.toString());
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
            SExpression expr = new SExpression(new Token("assert"),
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
        // smtStr += SExpressionConstants.AUTO_CONFIG_FALSE.toString();
        // smtStr += SExpressionConstants.SET_OPTION_PROPAGATE_BOOLEANS_FALSE
        // .toString();
        // smtStr += SExpressionConstants.SET_OPTION_PROPAGATE_VALUES_FALSE
        // .toString();
        smtStr += SExpressionConstants.DECLARE_SORT_VALUE.toString();

        smtStr += declarationStr;

        smtStr += assertPartition;

        smtStr += SExpressionConstants.APPLY_TSEITIN.toString();

        smtStr += SExpressionConstants.EXIT.toString();

        // DEBUG
        try {
            FileWriter fstream = new FileWriter("tmp.smt2");
            fstream.write(smtStr);
            fstream.close();
        } catch (IOException exc) {
            System.err.println("Error while writing to file tmp.smt2. ");
            exc.printStackTrace();
            noErrors = false;
        }
        // END DEBUG

        return smtStr;
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

        Timer timer = new Timer();

        // Flattening formula, because macros cause problems when
        // replacing arrays with uninterpreted functions
        // (functions cannot be macro parameters)
        System.out.println("  Flattening formula...");
        timer.start();
        Formula formula = logicParser.getMainFormula().flatten();
        timer.end();
        System.out.println("    Done. (" + timer + ")");
        assert (formula.getFunctionMacros().size() == 0);
        Set<Token> noDependenceVars = new HashSet<Token>(
                logicParser.getNoDependenceVariables());

        Set<Formula> constraints = new HashSet<Formula>();
        System.out.println("  Making array reads simple...");
        timer.reset();
        timer.start();
        formula.makeArrayReadsSimple(formula, constraints, noDependenceVars);
        timer.end();
        System.out.println("    Done. (" + timer + ")");
        System.out.println("  Removing array writes...");
        timer.reset();
        timer.start();
        formula.removeArrayWrites(formula, constraints, noDependenceVars);
        if (constraints.size() > 0) {
            List<Formula> constraintsList = new ArrayList<Formula>();
            constraintsList.addAll(constraints);
            AndFormula arrayConstraints = new AndFormula(constraintsList);
            formula = new ImpliesFormula(arrayConstraints, formula);
        }
        timer.end();
        System.out.println("    Done. (" + timer + ")");

        System.out.println("  Removing array equalities...");
        timer.reset();
        timer.start();
        formula.removeArrayEqualities();
        timer.end();
        System.out.println("    Done. (" + timer + ")");

        Set<DomainTerm> indexSet = formula.getIndexSet();

        lambda = new DomainVariable(Util.freshVarName(formula, "lambda"));

        List<Formula> lambdaDisequalities = new ArrayList<Formula>();
        for (DomainTerm index : indexSet) {
            List<DomainTerm> domainTerms = new ArrayList<DomainTerm>(2);
            domainTerms.add(lambda);
            domainTerms.add(index);
            lambdaDisequalities.add(new DomainEq(domainTerms, false));
        }
        Formula lambdaConstraints = new AndFormula(lambdaDisequalities);
        indexSet.add(lambda);
        noDependenceVars.add(new Token(lambda.getVarName()));

        System.out
                .println("  Converting array properties to finite conjunctions...");
        timer.reset();
        timer.start();
        formula.arrayPropertiesToFiniteConjunctions(indexSet);
        timer.end();
        System.out.println("    Done. (" + timer + ")");

        formula = new ImpliesFormula(lambdaConstraints, formula);

        Set<Token> currentDependenceArrayVariables = new HashSet<Token>();
        for (ArrayVariable var : formula.getArrayVariables())
            if (!noDependenceVars.contains(new Token(var.getVarName())))
                currentDependenceArrayVariables
                        .add(new Token(var.getVarName()));
        System.out
                .println("  Converting array reads to uninterpreted function calls...");
        timer.reset();
        timer.start();
        formula.arrayReadsToUninterpretedFunctions(noDependenceVars);
        noDependenceVars.removeAll(currentDependenceArrayVariables);
        timer.end();
        System.out.println("    Done. (" + timer + ")");

        List<PropositionalVariable> controlSignals = logicParser
                .getControlVariables();

        if (controlSignals.size() > 30) {
            throw new SuraqException(
                    "Current implementation cannot handle more than 30 control signals.");
        }

        outputExpressions = new ArrayList<SExpression>();
        // outputExpressions.add(SExpression.fromString("(set-logic QF_AUFLIA)"));

        outputExpressions.add(SExpressionConstants.SET_LOGIC_QF_UF);
        outputExpressions.add(SExpressionConstants.AUTO_CONFIG_FALSE);
        outputExpressions.add(SExpressionConstants.PROOF_MODE_2);
        // outputExpressions
        // .add(SExpressionConstants.SET_OPTION_PRODUCE_INTERPOLANT);
        outputExpressions.add(SExpressionConstants.DECLARE_SORT_VALUE);

        System.out.println("  Writing declarations...");

        int beginDeclarationsIdx = outputExpressions.size();

        timer.reset();
        timer.start();
        writeDeclarationsAndDefinitions(formula, noDependenceVars,
                controlSignals.size());
        timer.end();
        System.out.println("    Done. (" + timer + ")");

        // get declarations and functions
        ListIterator<SExpression> beginDeclarations = outputExpressions
                .listIterator(beginDeclarationsIdx);
        while (beginDeclarations.hasNext()) {
            SExpression elem = beginDeclarations.next();
            declarationStr += elem.toString();
        }

        int beginAssertPartitionIdx = outputExpressions.size();
        writeAssertPartitions(formula, noDependenceVars, controlSignals);

        // get assert partitions and transform to simplifies.
        ListIterator<SExpression> beginAssert = outputExpressions
                .listIterator(beginAssertPartitionIdx);
        while (beginAssert.hasNext()) {
            SExpression expr = beginAssert.next().deepCopy();
            // expr.replaceChild(new Token("simplify"), 0);
            assertPartitionList.add(expr);
        }

        outputExpressions.add(SExpressionConstants.CHECK_SAT);
        outputExpressions.add(SExpressionConstants.GET_PROOF);
        outputExpressions.add(SExpressionConstants.EXIT);

        return formula;
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

        if (outputExpressions == null)
            throw new SuraqException("outputExpressions not initialized!");

        for (int count = 0; count < (1 << controlSignals.size()); count++) {
            System.out.println("  Writing assert-partition number " + count);
            Formula tempFormula = formula.deepFormulaCopy();
            Map<Token, Term> variableSubstitutions = new HashMap<Token, Term>();
            for (Token var : noDependenceVars) {
                if (noDependenceVarsCopies.containsKey(var))
                    // it's a variable
                    variableSubstitutions.put(var,
                            noDependenceVarsCopies.get(var).get(count));
                else if (noDependenceFunctionsCopies.containsKey(var))
                    // it's an uninterpreted function
                    tempFormula.substituteUninterpretedFunction(var,
                            noDependenceFunctionsCopies.get(var).get(count));
                else
                    throw new SuraqException(
                            "noDependenceVar "
                                    + var.toString()
                                    + " is neither a variable nor an uninterpreted function.");
            }

            int currentCount = count;
            int mask = 1;
            for (int signalCount = 0; signalCount < controlSignals.size(); signalCount++) {
                variableSubstitutions
                        .put(new Token(controlSignals.get(signalCount)
                                .getVarName()), new PropositionalConstant(
                                (currentCount & mask) != 0));
                currentCount = currentCount >> 1;
            }

            tempFormula = tempFormula.substituteFormula(variableSubstitutions);
            tempFormula = new NotFormula(tempFormula);
            this.assertPartitionFormulas.put(count + 1, tempFormula);
            SExpression assertPartitionExpression = new SExpression();
            assertPartitionExpression.addChild(SExpressionConstants.ASSERT);
            // .addChild(SExpressionConstants.ASSERT_PARTITION);
            assertPartitionExpression.addChild(tempFormula.toSmtlibV2());
            outputExpressions.add(assertPartitionExpression);
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

        if (outputExpressions == null)
            throw new SuraqException("outputExpressions not initialized!");

        varTypes = new HashMap<Token, SExpression>();
        varTypes.put(new Token(lambda.getVarName()),
                SExpressionConstants.VALUE_TYPE);
        Map<Token, Integer> functionArity = new HashMap<Token, Integer>();

        for (PropositionalVariable var : formula.getPropositionalVariables()) {
            if (noDependenceVars.contains(var.toSmtlibV2())) {
                varTypes.put(new Token(var.getVarName()),
                        SExpressionConstants.BOOL_TYPE);
                continue; // noDependenceVars will be handled later.
            }
            outputExpressions
                    .add(SExpression.makeDeclareFun((Token) var.toSmtlibV2(),
                            SExpressionConstants.BOOL_TYPE, 0));
        }

        for (DomainVariable var : formula.getDomainVariables()) {
            if (noDependenceVars.contains(var.toSmtlibV2())) {
                varTypes.put(new Token(var.getVarName()),
                        SExpressionConstants.VALUE_TYPE);
                continue; // noDependenceVars will be handled later.
            }
            outputExpressions.add(SExpression.makeDeclareFun(
                    (Token) var.toSmtlibV2(), SExpressionConstants.VALUE_TYPE,
                    0));
        }

        // DEBUG
        // For debugging purposes, also handle array variables
        // (so that performing only some of the reductions can be tested)
        for (ArrayVariable var : formula.getArrayVariables()) {
            if (noDependenceVars.contains(var.toSmtlibV2())) {
                varTypes.put(new Token(var.getVarName()),
                        SExpressionConstants.ARRAY_TYPE);
                continue; // noDependenceVars will be handled later.
            }
            outputExpressions.add(SExpression.makeDeclareFun(
                    (Token) var.toSmtlibV2(), SExpressionConstants.ARRAY_TYPE,
                    0));
        } // end debug

        for (UninterpretedFunction function : formula
                .getUninterpretedFunctions()) {
            if (noDependenceVars.contains(function.getName())) {
                varTypes.put(new Token(function.getName()),
                        SExpressionConstants.VALUE_TYPE);
                functionArity.put(function.getName(), function.getNumParams());
                continue; // noDependenceVars will be handled later.
            }
            outputExpressions.add(SExpression.makeDeclareFun(
                    function.getName(), function.getType(),
                    function.getNumParams()));
        }

        // Now dealing with noDependenceVars
        noDependenceVarsCopies = new HashMap<Token, List<Term>>();
        noDependenceFunctionsCopies = new HashMap<Token, List<UninterpretedFunction>>();
        for (Token var : noDependenceVars) {
            SExpression type = varTypes.get(var);
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

            for (int count = 1; count <= (1 << numControlSignals); count++) {
                String name = Util.freshVarName(formula, var.toString()
                        + "_copy_" + count);
                outputExpressions.add(SExpression.makeDeclareFun(
                        new Token(name), type, numParams));
                if (numParams == 0) {
                    if (type.equals(SExpressionConstants.BOOL_TYPE))
                        listOfVarCopies.add(new PropositionalVariable(name,
                                count));
                    else if (type.equals(SExpressionConstants.VALUE_TYPE))
                        listOfVarCopies.add(new DomainVariable(name, count));
                    else {
                        assert (type.equals(SExpressionConstants.ARRAY_TYPE));
                        listOfVarCopies.add(new ArrayVariable(name, count));
                    }
                } else {
                    assert (type instanceof Token);
                    listOfFunctionCopies.add(new UninterpretedFunction(name,
                            numParams, (Token) type, count));
                }
            }
        }

        for (FunctionMacro macro : formula.getFunctionMacros())
            outputExpressions.add(macro.toSmtlibV2());
    }

    /**
     * Prints a final message.
     * 
     * @param result
     *            <code>true</code> if there were no errors, <code>false</code>
     *            otherwise.
     */
    private void printEnd(boolean result) {
        System.out
                .println("################################################################################");
        // System.out.println("Synthesis completed successfully!");
        System.out.println("");
        if (result)
            System.out.println("LIVE LONG AND PROSPER!");
        else
            System.out.println("There were errors.\nRESISTANCE IS FUTILE!");
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
     * @param propsitionalVars
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
    private Z3Proof parseProof(String proofStr,
            Set<PropositionalVariable> propsitionalVars,
            Set<DomainVariable> domainVars, Set<ArrayVariable> arrayVars,
            Set<UninterpretedFunction> uninterpretedFunctions) {
        // expression parsing of proof
        SExpParser sExpProofParser = null;
        sExpProofParser = new SExpParser(proofStr);

        Timer timer = new Timer();

        try {
            System.out.println("  Parsing proof to S-Expressions...");
            timer.start();
            sExpProofParser.parse();
            assert (sExpProofParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            noErrors = false;
        } finally {
            timer.end();
            System.out.println("    Done. (" + timer + ")");
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
            System.out.println("  Parsing proof to SMTLIB objects...");
            timer.start();
            proofParser.parse();
            assert (proofParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            noErrors = false;
            throw new RuntimeException("Unable to parse proof!");
        } finally {
            timer.end();
            System.out.println("    Done. (" + timer + ")");
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
    private void printProofSize(Z3Proof proof) {

        SuraqOptions options = SuraqOptions.getInstance();

        if (options.isVerbose()) {
            DecimalFormat myFormatter = new DecimalFormat("###,###,###");
            Timer dagTimer = new Timer();
            dagTimer.start();
            int dagSize = proof.size(false);
            dagTimer.end();
            String dagSizeString = myFormatter.format(dagSize);
            System.out.println("    Proof (DAG)  size: " + dagSizeString
                    + " (computed in " + dagTimer + ")");
            Timer treeTimer = new Timer();
            treeTimer.start();
            int treeSize = proof.size(true);
            treeTimer.end();
            String treeSizeString = myFormatter.format(treeSize);
            System.out.println("    Proof (tree) size: " + treeSizeString
                    + " (computed in " + treeTimer + ")");
            System.out.println();
        }
    }
}
