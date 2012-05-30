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
import at.iaik.suraq.resProof.ResProof;
import at.iaik.suraq.resProof.ResProofTest;
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
import at.iaik.suraq.smtlib.formula.PropositionalConstant;
import at.iaik.suraq.smtlib.formula.PropositionalIte;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtsolver.SMTSolver;
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
     * stores the assert partitions of the smt description
     */
    private List<String> assertPartitionStrList = new ArrayList<String>();

    private Formula mainFormula = null;

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

        try {
            sExpParser.parse();
            assert (sExpParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            noErrors = false;
            return null;
        }

        logicParser = new LogicParser(sExpParser.getRootExpr());

        try {
            logicParser.parse();
            assert (logicParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            noErrors = false;
            return null;
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

        SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type, "lib/z3/bin/z3");

        System.out.println("  Simplifying assert-partitions...");
        List<String> simplifiedAssertPartitions = new ArrayList<String>();
        for (String assertPartition : assertPartitionStrList) {
            String smtStr = buildSimplifySMTDescription(declarationStr,
                    assertPartition);
            String simpleSmtStr = z3.simplify(smtStr);
            simplifiedAssertPartitions.add(simpleSmtStr);

        }
        String z3InputStr = buildProofSMTDescription(declarationStr,
                simplifiedAssertPartitions);

        return z3InputStr;
    }

    private Map<PropositionalVariable, PropositionalIte> proofTransformationAndInterpolation(
            String proof) {
        // expression parsing of proof
        SExpParser sExpProofParser = null;
        sExpProofParser = new SExpParser(proof);

        try {
            sExpProofParser.parse();
            assert (sExpProofParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            noErrors = false;
            return null;
        }

        // build function and variable lists for proof parser
        Set<PropositionalVariable> propsitionalVars = mainFormula
                .getPropositionalVariables();
        Set<DomainVariable> domainVars = mainFormula.getDomainVariables();
        Set<ArrayVariable> arrayVars = mainFormula.getArrayVariables();
        Set<UninterpretedFunction> uninterpretedFunctions = mainFormula
                .getUninterpretedFunctions();

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

        // parsing proof
        ProofParser proofParser = new ProofParser(
                sExpProofParser.getRootExpr(), domainVars, propsitionalVars,
                arrayVars, uninterpretedFunctions);

        try {
            proofParser.parse();
            assert (proofParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            noErrors = false;
            return null;
        }

        // Main Flow
        Z3Proof rootProof = proofParser.getRootProof();
        // assert (rootProof.checkZ3ProofNodeRecursive);
        System.out.println("  Original Z3 Proof");
        System.out.println("  Proof DAG size: " + rootProof.size(false));
        System.out.println("  Proof size after unwinding DAG: "
                + rootProof.size(true));
        System.out.println();

        rootProof.localLemmasToAssertions();
        // assert (rootProof.checkZ3ProofNodeRecursive());
        System.out.println("  After localLemmasToAssertions()");
        System.out.println("  Proof DAG size: " + rootProof.size(false));
        System.out.println("  Proof size after unwinding DAG: "
                + rootProof.size(true));
        System.out.println();

        rootProof.removeLocalSubProofs();
        // assert (rootProof.checkZ3ProofNodeRecursive());
        System.out.println("  After removeLocalSubProofs()");
        System.out.println("  Proof DAG size: " + rootProof.size(false));
        System.out.println("  Proof size after unwinding DAG: "
                + rootProof.size(true));
        System.out.println();

        rootProof.dealWithModusPonens();
        // assert (rootProof.checkZ3ProofNodeRecursive());
        System.out.println("  After dealWithModusPonens()");
        System.out.println("  Proof DAG size: " + rootProof.size(false));
        System.out.println("  Proof size after unwinding DAG: "
                + rootProof.size(true));
        System.out.println();

        // System.out.println("Num Instances: " +
        // Z3Proof.numInstances());
        TransformedZ3Proof transformedZ3Proof = TransformedZ3Proof
                .convertToTransformedZ3Proof(rootProof);
        System.out.println("  After convertToTransformedZ3Proof()");
        System.out.println("  Proof DAG size: "
                + transformedZ3Proof.size(false));
        System.out.println("  Proof size after unwinding DAG: "
                + transformedZ3Proof.size(true));
        System.out.println();
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

        transformedZ3Proof.toLocalProof();
        // assert (transformedZ3Proof.checkZ3ProofNodeRecursive());

        System.out.println("  After toLocalProof()");
        System.out.println("  Proof DAG size: "
                + transformedZ3Proof.size(false));
        System.out.println("  Proof size after unwinding DAG: "
                + transformedZ3Proof.size(true));
        System.out.println();
        assert (transformedZ3Proof.isLocal());

        transformedZ3Proof.toResolutionProof();
        System.out.println("  After toResolutionProof()");
        System.out.println("  Proof DAG size: "
                + transformedZ3Proof.size(false));
        System.out.println("  Proof size after unwinding DAG: "
                + transformedZ3Proof.size(true));
        System.out.println();
        assert (transformedZ3Proof.checkZ3ProofNodeRecursive());

        // START: ASHUTOSH code
        ResProof resolutionProof = Util
                .createResolutionProof(transformedZ3Proof);

        // resolutionProof.dumpProof();
        resolutionProof.checkProof(false);
        resolutionProof.rmDoubleLits();
        resolutionProof.deLocalizeProof();
        resolutionProof.checkProof(false);
        resolutionProof.tranformResProofs();
        // END: ASHUTOSH code

        // Transform back into Z3Proof format
        TransformedZ3Proof recoveredProof = new TransformedZ3Proof(
                resolutionProof.getRoot(), Util.getLiteralMap());

        System.out.println("  After recovering proof:");
        System.out.println("  Proof DAG size: " + recoveredProof.size(false));
        System.out.println("  Proof size after unwinding DAG: "
                + recoveredProof.size(true));

        // create ITE-tree for every control signal
        Map<PropositionalVariable, PropositionalIte> iteTrees = recoveredProof
                .createITETrees(logicParser.getControlVariables());

        return iteTrees;
    }

    /**
     * @see java.lang.Runnable#run()
     */
    @Override
    public void run() {
        // START: ASHUTOSH code
        ResProofTest pTst = new ResProofTest();
        if (pTst.takeControl())
            return;
        // END: ASHUTOSH code
        printWelcome();

        SuraqOptions options = SuraqOptions.getInstance();

        File sourceFile = new File(options.getInput());
        if (options.isVerbose())
            System.out.println("Parsing input file " + sourceFile.toString());

        File z3InputFile = new File(options.getZ3Input());
        File z3ProofFile = new File(options.getZ3Proof());

        boolean useCachedResults = false;

        if (z3InputFile.exists() && z3ProofFile.exists()) {
            Date inputFileDate = new Date(sourceFile.lastModified());
            Date z3InputFileDate = new Date(z3InputFile.lastModified());
            Date z3ProofFileDate = new Date(z3ProofFile.lastModified());

            if ((inputFileDate.getTime() <= z3InputFileDate.getTime())
                    && (z3InputFileDate.getTime() <= z3ProofFileDate.getTime())) {

                useCachedResults = true;
                System.out.println("INFO: using cached intermediate results.");
            }
        }

        String proof = null;
        if (true) {
            // if (!useCachedResults) {
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

            SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type, "lib/z3/bin/z3");
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
        } else { // use cached files
            try {

                // read proof from file
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

                // parse z3input file
                SExpParser sExpParser = null;
                try {
                    sExpParser = new SExpParser(z3InputFile);
                } catch (FileNotFoundException exc) {
                    System.err.println("ERROR: File " + z3InputFile.getPath()
                            + " not found!");
                    noErrors = false;
                    return;
                } catch (IOException exc) {
                    System.err.println("ERROR: Could not read from file "
                            + z3InputFile.getPath());
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

                logicParser = new LogicParser(sExpParser.getRootExpr());

                try {
                    logicParser.parse();
                    assert (logicParser.wasParsingSuccessfull());
                } catch (ParseError exc) {
                    handleParseError(exc);
                    noErrors = false;
                    return;
                }
                this.mainFormula = logicParser.getMainFormula();

            } catch (IOException exc) {
                System.out.println("ERROR: Could not read cached proof!");
            }
        }

        System.out
                .println("start proof transformations and interpolation calculations.");
        Timer interpolationTimer = new Timer();
        interpolationTimer.start();

        assert (proof != null);

        Map<PropositionalVariable, PropositionalIte> iteTrees = proofTransformationAndInterpolation(proof);

        interpolationTimer.end();
        System.out
                .println("finished proof transformations and interpolation calculations in "
                        + interpolationTimer + ".\n");

        // write output file
        try {

            File smtfile = new File(options.getOutput());
            FileWriter fstream = new FileWriter(smtfile);
            BufferedWriter smtfilewriter = new BufferedWriter(fstream);
            for (PropositionalVariable controlVar : iteTrees.keySet())
                smtfilewriter.write(";" + controlVar.toString() + "\n"
                        + iteTrees.get(controlVar).toString() + "\n");
            smtfilewriter.close();
        } catch (IOException exc) {
            System.err.println("Error while writing to outputfile:"
                    + options.getOutput());
            exc.printStackTrace();
            noErrors = false;
        }

        System.out.println(" done!");

        // All done :-)
        printEnd(noErrors);
        return;
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
     * Creates an SMT description for an simplify operation
     * 
     * @param declarationStr
     *            declarations of the SMT description
     * @param assertPartition
     *            partition to be simplified
     * @return SMT description of simplify operation
     * 
     */
    private String buildSimplifySMTDescription(String declarationStr,
            String assertPartition) {
        String smtStr = "";

        smtStr += SExpressionConstants.SET_LOGIC_QF_UF.toString();
        smtStr += SExpressionConstants.AUTO_CONFIG_FALSE.toString();
        smtStr += SExpressionConstants.SET_OPTION_PROPAGATE_BOOLEANS_FALSE
                .toString();
        smtStr += SExpressionConstants.SET_OPTION_PROPAGATE_VALUES_FALSE
                .toString();
        smtStr += SExpressionConstants.DECLARE_SORT_VALUE.toString();

        smtStr += declarationStr;

        smtStr += assertPartition;

        smtStr += SExpressionConstants.EXIT.toString();

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

        // Flattening formula, because macros cause problems when
        // replacing arrays with uninterpreted functions
        // (functions cannot be macro parameters)
        System.out.println("  Flattening formula...");
        Formula formula = logicParser.getMainFormula().flatten();
        assert (formula.getFunctionMacros().size() == 0);
        Set<Token> noDependenceVars = new HashSet<Token>(
                logicParser.getNoDependenceVariables());

        Set<Formula> constraints = new HashSet<Formula>();
        System.out.println("  Making array reads simple...");
        formula.makeArrayReadsSimple(formula, constraints, noDependenceVars);
        System.out.println("  Removing array writes...");
        formula.removeArrayWrites(formula, constraints, noDependenceVars);
        if (constraints.size() > 0) {
            List<Formula> constraintsList = new ArrayList<Formula>();
            constraintsList.addAll(constraints);
            AndFormula arrayConstraints = new AndFormula(constraintsList);
            formula = new ImpliesFormula(arrayConstraints, formula);
        }

        System.out.println("  Removing array equalities...");
        formula.removeArrayEqualities();

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
        formula.arrayPropertiesToFiniteConjunctions(indexSet);

        formula = new ImpliesFormula(lambdaConstraints, formula);

        Set<Token> currentDependenceArrayVariables = new HashSet<Token>();
        for (ArrayVariable var : formula.getArrayVariables())
            if (!noDependenceVars.contains(new Token(var.getVarName())))
                currentDependenceArrayVariables
                        .add(new Token(var.getVarName()));
        System.out
                .println("  Converting array reads to uninterpreted function calls...");
        formula.arrayReadsToUninterpretedFunctions(noDependenceVars);
        noDependenceVars.removeAll(currentDependenceArrayVariables);

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

        writeDeclarationsAndDefinitions(formula, noDependenceVars,
                controlSignals.size());

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
            expr.replaceChild(new Token("simplify"), 0);
            assertPartitionStrList.add(expr.toString());
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
}
