/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.main;

import jargs.gnu.CmdLineParser;
import jargs.gnu.CmdLineParser.Option;
import jargs.gnu.CmdLineParser.OptionException;
import at.iaik.suraq.exceptions.SuraqException;

/**
 * A singleton class that stores the program options.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public final class SuraqOptions {

    /**
     * Constants for cache types
     */
    public static final int CACHE_NONE = 0;
    public static final int CACHE_FILE = 1;
    public static final int CACHE_SERIAL = 2;

    /**
     * Constants for tseitin types
     */
    public static final int TSEITIN_WITH_Z3 = 0;
    public static final int TSEITIN_WITHOUT_Z3 = 1;

    private static final boolean performAckermannDefault = false;
    private static final boolean performITEEquationReductionDefault = false;
    private static final boolean performGraphReductionDefault = false;
    private static final boolean performQBFEncoderDefault = false;
    private static final boolean performVeriTSolverDefault = false;

    private static final String dumpSMTQueryFileDefault = null;
    private static final boolean exitAfterDumpDefault = false;

    /**
     * Default value for verbose option.
     */
    private static final boolean verboseDefault = false;

    /**
     * Default value for checkResult option.
     */
    private static final boolean checkResultDefault = false;

    /**
     * Default value for cache option.
     */
    private static final int cacheDefault = SuraqOptions.CACHE_NONE;

    /**
     * Default value for tseitin option.
     */
    private static final int tseitinDefault = SuraqOptions.TSEITIN_WITHOUT_Z3;
    // private static final int tseitinDefault = SuraqOptions.TSEITIN_WITH_Z3;

    /**
     * Default value for input option.
     */
    private static String inputDefault = "suraq_input.smt2";

    /**
     * Default prefix value for z3input option.
     */
    private static String z3InputDefault = "suraq_z3_input.smt2";

    /**
     * Default value for z3proof option.
     */
    private static String z3ProofDefault = "suraq_z3_proof.smt2";

    /**
     * Default value for output option.
     */
    private static String outputDefault = "suraq_output.smt2";

    /**
     * Default value for solver option.
     */
    private static final String solverDefault = "veriT";

    /**
     * Default value for newVeritCache option.
     */
    private static final boolean newVeritCacheDefault = false;

    /**
     * Default value for removeLemmaSubproofs option.
     */
    private static final boolean dontRemoveLemmaSubproofsDefault = false;

    /**
     * Default value for performing iterative interpolation
     */
    private static final boolean iterativeInterpolationDefault = false;

    /**
     * Default value for checkProofWhileParsing option.
     */
    private static final boolean checkProofWhileParsingDefault = false;

    /**
     * Default value for the number of splitter threads
     */
    private static final int numSplitterThreadsDefault = 1;

    /**
     * Default value for the sleep time of the splitter bookkeeper
     */
    private static final int splitterBookkeeperSleepTimeDefault = 120;

    /**
     * The cache file name.
     */
    private static String cacheFile = "savecache.db";

    /**
     * The cache serial file name.
     */
    private static String cacheFileSerial = "savecache.serial.db";

    private final Boolean performAckermann;
    private final Boolean performITEEquationReduction;
    private final Boolean performGraphReduction;
    private final Boolean performQBFEncoder;
    private final Boolean performVeriTSolver;

    private final String veriTVars;
    private final String veriTFile;

    /**
     * The value of the verbose option.
     */
    private final Boolean verboseValue;

    /**
     * The value of the checkResult option.
     */
    private final Boolean checkResultValue;

    /**
     * The value of the keepTempFiles option.
     */
    private final Boolean keepTempFilesValue;

    /**
     * The value of the cache option.
     */
    private final Integer cacheValue;

    /**
     * The value of the tseitin option.
     */
    private final Integer tseitinValue;

    /**
     * The value of the input option.
     */
    private final String inputValue;

    /**
     * The value of the z3input option.
     */
    private final String z3InputValue;

    /**
     * The value of the z3proof option.
     */
    private final String z3ProofValue;

    /**
     * The value of the output option.
     */
    private final String outputValue;

    private final String useThisProofFileValue;

    private final String useThisPropProofFileValue;

    /**
     * The value of the solver option.
     */
    private final String solverValue;

    /**
     * The value of the newVeritCache option.
     */
    private final Boolean newVeritCacheValue;

    /**
     * the value of removeLemmaSubproofs
     */
    private final Boolean dontRemoveLemmaSubproofs;

    /**
     * the value of the option for performing iterative interpolation
     */
    private final Boolean iterativeInterpolation;

    /**
     * the value of checkProofWhileParsing
     */
    private final Boolean checkProofWhileParsing;

    private final Boolean checkLeafInterpolants;

    private final Boolean checkResolutionInterpolants;

    private final Boolean checkTseitinValue;

    /**
     * The value of numSplitterThreads
     */
    private final Integer numSplitterThreadsValue;

    /**
     * The value of splitterBookkeeperSleepTime
     */
    private final Integer splitterBookkeeperSleepTimeValue;

    /**
     * The value of the dumpSMTQueryFile option.
     */
    private final String dumpSMTQueryFileValue;

    /**
     * The value of the exitAfterDumpValue option.
     */
    private final Boolean exitAfterDumpValue;

    /**
     * The parser that stores the (parsed) command-line options.
     */
    private final CmdLineParser cmdLineParser = new CmdLineParser();

    /**
     * The single instance of this class.
     */
    private static SuraqOptions instance;

    /**
     * The path to z3.2 solver.
     */
    private static final String z3Path = "lib/z3/bin/z3";

    /**
     * The path to z3.4 solver.
     */
    private static final String z3_4Path = "lib/z3-4.0/bin/z3";

    public static void reset() {
        SuraqOptions.inputDefault = "suraq_input.smt2";
        SuraqOptions.z3InputDefault = "suraq_z3_input.smt2";
        SuraqOptions.z3ProofDefault = "suraq_z3_proof.smt2";
        SuraqOptions.outputDefault = "suraq_output.smt2";
        SuraqOptions.cacheFile = "savecache.db";
        SuraqOptions.cacheFileSerial = "savecache.serial.db";
    }

    /**
     * 
     * Constructs the singleton <code>SuraqOptions</code> instance.
     * 
     * @param args
     *            the command-line arguments.
     * @throws SuraqException
     *             if parsing fails.
     */
    private SuraqOptions(String[] args) throws SuraqException {
        if (SuraqOptions.instance != null)
            throw new RuntimeException(
                    "Trying to instantiate second copy of singleton class SuraqOptions.");

        if (args == null)
            args = new String[0];

        Option inputOption = cmdLineParser.addStringOption('i', "input");
        Option z3InputOption = cmdLineParser.addStringOption("z3input");
        Option z3ProofOption = cmdLineParser.addStringOption("z3proof");
        Option outputOption = cmdLineParser.addStringOption('o', "output");
        Option verboseOption = cmdLineParser.addBooleanOption('v', "verbose");
        Option checkResultOption = cmdLineParser
                .addBooleanOption("check_result");
        Option cacheOption = cmdLineParser.addIntegerOption('c', "cache");
        Option tseitinOption = cmdLineParser.addIntegerOption("tseitin");

        Option ackermannOption = cmdLineParser
                .addBooleanOption("perform-ackermann");
        Option itereductionOption = cmdLineParser
                .addBooleanOption("perform-itereduction");
        Option graphReductionOption = cmdLineParser
                .addBooleanOption("perform-graphreduction");
        Option qbfOption = cmdLineParser.addBooleanOption("perform-qbf");
        Option veriTOption = cmdLineParser.addBooleanOption("perform-verit");

        Option veriTVarsCache = cmdLineParser.addStringOption("veriTVarsCache");
        Option veriTFileOption = cmdLineParser.addStringOption("veriTFile");

        Option solverOption = cmdLineParser.addStringOption("solver");

        Option newVeritCacheOption = cmdLineParser
                .addBooleanOption("newVeritCache");

        Option dontRemoveLemmaSubproofsOption = cmdLineParser
                .addBooleanOption("dontRemoveLemmaSubproofs");

        Option iterativeInterpolationOption = cmdLineParser
                .addBooleanOption("iterative");

        Option dumpSMTQueryFileOption = cmdLineParser
                .addStringOption("dumpSMTQueryFile");

        Option exitAfterDumpOption = cmdLineParser
                .addBooleanOption("exitAfterDump");

        Option checkProofWhileParsingOption = cmdLineParser
                .addBooleanOption("checkProofWhileParsing");

        Option checkLeafInterpolantsOption = cmdLineParser
                .addBooleanOption("checkLeafInterpolants");

        Option checkResolutionInterpolantsOption = cmdLineParser
                .addBooleanOption("checkResolutionInterpolants");

        Option checkTseitinOption = cmdLineParser
                .addBooleanOption("checkTseitin");

        Option useThisProofFileOption = cmdLineParser
                .addStringOption("useThisProofFile");

        Option useThisPropProofFileOption = cmdLineParser
                .addStringOption("useThisPropProofFile");

        Option numSplitterThreadsOption = cmdLineParser
                .addIntegerOption("numSplitterThreads");

        Option splitterBookkeeperSleepTimeOption = cmdLineParser
                .addIntegerOption("splitterBookkeeperSleepTime");

        Option keepTempFilesOption = cmdLineParser
                .addBooleanOption("keepTempFiles");

        try {
            cmdLineParser.parse(args);
        } catch (OptionException exc) {
            throw new SuraqException("Error in parsing options.", exc);
        }

        performAckermann = (Boolean) cmdLineParser
                .getOptionValue(ackermannOption);
        performITEEquationReduction = (Boolean) cmdLineParser
                .getOptionValue(itereductionOption);
        performGraphReduction = (Boolean) cmdLineParser
                .getOptionValue(graphReductionOption);
        performQBFEncoder = (Boolean) cmdLineParser.getOptionValue(qbfOption);
        performVeriTSolver = (Boolean) cmdLineParser
                .getOptionValue(veriTOption);

        inputValue = (String) cmdLineParser.getOptionValue(inputOption);
        z3InputValue = (String) cmdLineParser.getOptionValue(z3InputOption);
        z3ProofValue = (String) cmdLineParser.getOptionValue(z3ProofOption);
        outputValue = (String) cmdLineParser.getOptionValue(outputOption);
        verboseValue = (Boolean) cmdLineParser.getOptionValue(verboseOption);
        checkResultValue = (Boolean) cmdLineParser
                .getOptionValue(checkResultOption);
        cacheValue = (Integer) cmdLineParser.getOptionValue(cacheOption);
        tseitinValue = (Integer) cmdLineParser.getOptionValue(tseitinOption);

        veriTVars = (String) cmdLineParser.getOptionValue(veriTVarsCache);
        veriTFile = (String) cmdLineParser.getOptionValue(veriTFileOption);

        solverValue = (String) cmdLineParser.getOptionValue(solverOption);

        newVeritCacheValue = (Boolean) cmdLineParser
                .getOptionValue(newVeritCacheOption);

        dontRemoveLemmaSubproofs = (Boolean) cmdLineParser
                .getOptionValue(dontRemoveLemmaSubproofsOption);

        iterativeInterpolation = (Boolean) cmdLineParser
                .getOptionValue(iterativeInterpolationOption);

        checkProofWhileParsing = (Boolean) cmdLineParser
                .getOptionValue(checkProofWhileParsingOption);

        checkLeafInterpolants = (Boolean) cmdLineParser
                .getOptionValue(checkLeafInterpolantsOption);

        checkResolutionInterpolants = (Boolean) cmdLineParser
                .getOptionValue(checkResolutionInterpolantsOption);

        checkTseitinValue = (Boolean) cmdLineParser
                .getOptionValue(checkTseitinOption);

        dumpSMTQueryFileValue = (String) cmdLineParser
                .getOptionValue(dumpSMTQueryFileOption);

        exitAfterDumpValue = (Boolean) cmdLineParser
                .getOptionValue(exitAfterDumpOption);

        useThisProofFileValue = (String) cmdLineParser
                .getOptionValue(useThisProofFileOption);

        useThisPropProofFileValue = (String) cmdLineParser
                .getOptionValue(useThisPropProofFileOption);

        numSplitterThreadsValue = (Integer) cmdLineParser
                .getOptionValue(numSplitterThreadsOption);

        splitterBookkeeperSleepTimeValue = (Integer) cmdLineParser
                .getOptionValue(splitterBookkeeperSleepTimeOption);

        keepTempFilesValue = (Boolean) cmdLineParser
                .getOptionValue(keepTempFilesOption);

        int end = getInput().lastIndexOf(".");

        SuraqOptions.z3InputDefault = getInput().substring(0, end) + '_'
                + SuraqOptions.z3InputDefault;
        SuraqOptions.z3ProofDefault = getInput().substring(0, end) + '_'
                + SuraqOptions.z3ProofDefault;
        SuraqOptions.outputDefault = getInput().substring(0, end) + '_'
                + SuraqOptions.outputDefault;
        SuraqOptions.cacheFile = getInput().substring(0, end) + '_'
                + SuraqOptions.cacheFile;
        SuraqOptions.cacheFileSerial = getInput().substring(0, end) + '_'
                + SuraqOptions.cacheFileSerial;
    }

    /**
     * Returns the singleton instance of this class. Creates it, when necessary.
     * 
     * @return The singleton instance of this class.
     */
    public static SuraqOptions getInstance() {
        if (SuraqOptions.instance == null)
            try {
                SuraqOptions.instance = new SuraqOptions(null);
            } catch (SuraqException exc) {
                throw new RuntimeException(
                        "Unexpected exception while trying to create default option object.",
                        exc);
            }
        return SuraqOptions.instance;
    }

    /**
     * Initializes the singleton instance with the given arguments.
     * 
     * @param args
     *            the command-line arguments
     * @throws SuraqException
     *             when the singleton instance is already initialized
     */
    public static void initialize(String[] args) throws SuraqException {
        if (SuraqOptions.instance != null)
            throw new SuraqException("Options already initialized!");
        SuraqOptions.instance = new SuraqOptions(args);
    }

    /**
     * Kills the instance.
     */
    public static void kill() {
        SuraqOptions.instance = null;
    }

    /**
     * Returns the value of the verbose option.
     * 
     * @return the value of the verbose option.
     */
    public boolean isVerbose() {
        return verboseValue != null ? verboseValue
                : SuraqOptions.verboseDefault;
    }

    /**
     * Returns the value of the checkResult option.
     * 
     * @return the value of the checkResult option.
     */
    public boolean isCheckResult() {
        return checkResultValue != null ? checkResultValue
                : SuraqOptions.checkResultDefault;
    }

    /**
     * Returns the value of the cache option.
     * 
     * @return the value of the cache option.
     */
    public int getCacheType() {
        return cacheValue != null ? cacheValue : SuraqOptions.cacheDefault;
    }

    /**
     * Returns the value of the tseitin option.
     * 
     * @return the value of the tseitin option.
     */
    public int getTseitinType() {
        return tseitinValue != null ? tseitinValue
                : SuraqOptions.tseitinDefault;
    }

    /**
     * Returns the value of the input option.
     * 
     * @return the value of the input option.
     */
    public String getInput() {
        return inputValue != null ? inputValue : SuraqOptions.inputDefault;
    }

    /**
     * Returns the value of the z3input option.
     * 
     * @return the value of the z3input option.
     */
    public String getZ3Input() {
        return z3InputValue != null ? z3InputValue
                : SuraqOptions.z3InputDefault;
    }

    /**
     * Returns the value of the z3proof option.
     * 
     * @return the value of the z3proof option.
     */
    public String getZ3Proof() {
        return z3ProofValue != null ? z3ProofValue
                : SuraqOptions.z3ProofDefault;
    }

    /**
     * Returns the filename of the cache file.
     * 
     * @return the filename of the cache file.
     */
    public String getCacheFile() {
        return SuraqOptions.cacheFile;
    }

    /**
     * Returns the filename of the serial cache file.
     * 
     * @return the filename of the serial cache file.
     */
    public String getCacheFileSerial() {
        return SuraqOptions.cacheFileSerial;
    }

    /**
     * Returns the value of the output option.
     * 
     * @return the value of the output option.
     */
    public String getOutput() {
        return outputValue != null ? outputValue : SuraqOptions.outputDefault;
    }

    /**
     * Returns the path of the Z3.2 solver.
     * 
     * @return the path of the Z3.2 solver.
     */
    public static String getZ3Path() {
        return SuraqOptions.z3Path;
    }

    /**
     * Returns the path of the Z3.4 solver.
     * 
     * @return the path of the Z3.4 solver.
     */
    public static String getZ3_4Path() {
        return SuraqOptions.z3_4Path;
    }

    public Boolean getPerformAckermann() {
        if (performAckermann == null)
            return SuraqOptions.performAckermannDefault;
        return performAckermann;
    }

    public Boolean getPerformITEEquationReduction() {
        if (performITEEquationReduction == null)
            return SuraqOptions.performITEEquationReductionDefault;
        return performITEEquationReduction;
    }

    public Boolean getPerformGraphReduction() {
        if (performGraphReduction == null)
            return SuraqOptions.performGraphReductionDefault;
        return performGraphReduction;
    }

    public Boolean getPerformQBFEncoder() {
        if (performQBFEncoder == null)
            return SuraqOptions.performQBFEncoderDefault;
        return performQBFEncoder;
    }

    public Boolean getPerformVeriTSolver() {
        if (performVeriTSolver == null)
            return SuraqOptions.performVeriTSolverDefault;
        return performVeriTSolver;
    }

    public String getVeriTVarsCache() {
        return veriTVars;
    }

    public String getVeriTFile() {
        return veriTFile;
    }

    public String getSolver() {
        return solverValue == null ? SuraqOptions.solverDefault : solverValue;
    }

    public boolean useNewVeritCache() {
        return newVeritCacheValue == null ? SuraqOptions.newVeritCacheDefault
                : newVeritCacheValue;
    }

    public boolean getDontRemoveLemmaSubproofs() {
        return dontRemoveLemmaSubproofs == null ? SuraqOptions.dontRemoveLemmaSubproofsDefault
                : dontRemoveLemmaSubproofs;
    }

    public boolean getIterativeInterpolation() {
        return iterativeInterpolation == null ? SuraqOptions.iterativeInterpolationDefault
                : iterativeInterpolation;
    }

    public String getDumpSMTQueryFile() {
        return dumpSMTQueryFileValue == null ? SuraqOptions.dumpSMTQueryFileDefault
                : dumpSMTQueryFileValue;
    }

    public boolean getExitAfterDump() {
        return exitAfterDumpValue == null ? SuraqOptions.exitAfterDumpDefault
                : exitAfterDumpValue;
    }

    public boolean getCheckProofWhileParsing() {
        return checkProofWhileParsing == null ? SuraqOptions.checkProofWhileParsingDefault
                : checkProofWhileParsing;
    }

    public boolean getCheckLeafInterpolants() {
        return checkLeafInterpolants == null ? false : checkLeafInterpolants;
    }

    public boolean getCheckResolutionInterpolants() {
        return checkResolutionInterpolants == null ? false
                : checkResolutionInterpolants;
    }

    public boolean getCheckTseitin() {
        return checkTseitinValue == null ? false : checkTseitinValue;
    }

    public boolean getKeepTemFiles() {
        return keepTempFilesValue == null ? false : keepTempFilesValue;
    }

    public int getNumSplitterThreads() {
        return numSplitterThreadsValue == null ? SuraqOptions.numSplitterThreadsDefault
                : numSplitterThreadsValue;
    }

    public int getSplitterBookkeeperSleepTime() {
        return splitterBookkeeperSleepTimeValue == null ? SuraqOptions.splitterBookkeeperSleepTimeDefault
                : splitterBookkeeperSleepTimeValue;
    }

    /**
     * 
     * @return The name of the file to read the proof from (instead of calling a
     *         solver), or <code>null</code> if the solver should be called.
     */
    public String getUseThisProofFile() {
        return useThisProofFileValue;
    }

    /**
     * 
     * @return The name of the file to read into a ResProof.
     */
    public String getUseThisPropProofFile() {
        return useThisPropProofFileValue;
    }

    /**
     * @return
     */
    public String getInputWithoutExtension() {
        String input = this.getInput();
        int index = input.lastIndexOf(".");
        return input.substring(0, index);
    }
}
