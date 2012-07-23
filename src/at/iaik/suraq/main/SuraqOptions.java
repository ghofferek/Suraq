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
    private static final int tseitinDefault = SuraqOptions.TSEITIN_WITHOUT_Z3; // FIXME: changed by chillebold 19.07.2012
    //private static final int tseitinDefault = SuraqOptions.TSEITIN_WITH_Z3; // FIXME: changed by chillebold 19.07.2012

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
     * The cache file name.
     */
    private static String cacheFile = "savecache.db";

    /**
     * The cache serial file name.
     */
    private static String cacheFileSerial = "savecache.serial.db";

    /**
     * The value of the verbose option.
     */
    private final Boolean verboseValue;

    /**
     * The value of the checkResult option.
     */
    private final Boolean checkResultValue;

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

    public static void reset()
    {   
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

        try {
            cmdLineParser.parse(args);
        } catch (OptionException exc) {
            throw new SuraqException("Error in parsing options.", exc);
        }

        inputValue = (String) cmdLineParser.getOptionValue(inputOption);
        z3InputValue = (String) cmdLineParser.getOptionValue(z3InputOption);
        z3ProofValue = (String) cmdLineParser.getOptionValue(z3ProofOption);
        outputValue = (String) cmdLineParser.getOptionValue(outputOption);
        verboseValue = (Boolean) cmdLineParser.getOptionValue(verboseOption);
        checkResultValue = (Boolean) cmdLineParser
                .getOptionValue(checkResultOption);
        cacheValue = (Integer) cmdLineParser.getOptionValue(cacheOption);
        tseitinValue = (Integer) cmdLineParser.getOptionValue(tseitinOption);

        if(inputValue != null) // ch
        {
	        int end = inputValue.lastIndexOf(".");
	
	        SuraqOptions.z3InputDefault = inputValue.substring(0, end) + '_'
	                + SuraqOptions.z3InputDefault;
	        SuraqOptions.z3ProofDefault = inputValue.substring(0, end) + '_'
	                + SuraqOptions.z3ProofDefault;
	        SuraqOptions.outputDefault = inputValue.substring(0, end) + '_'
	                + SuraqOptions.outputDefault;
	        SuraqOptions.cacheFile = inputValue.substring(0, end) + '_'
	                + SuraqOptions.cacheFile;
	        SuraqOptions.cacheFileSerial = inputValue.substring(0, end) + '_'
	                + SuraqOptions.cacheFileSerial;
        }
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

}
