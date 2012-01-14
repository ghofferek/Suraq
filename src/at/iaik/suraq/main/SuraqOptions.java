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
public class SuraqOptions {

    /**
     * Default value for verbose option.
     */
    private static final boolean verboseDefault = false;

    /**
     * The value of the verbose option.
     */
    private final Boolean verboseValue;

    /**
     * Default value for input option.
     */
    private static final String inputDefault = "suraq.smt2";

    /**
     * The value of the input option.
     */
    private final String inputValue;

    /**
     * Default value for smtfile option.
     */
    private static final String smtfileDefault = "suraq_qf_uf.smt2";

    /**
     * The value of the smtfile option.
     */
    private final String smtfileValue;

    /**
     * The parser that stores the (parsed) command-line options.
     */
    private final CmdLineParser cmdLineParser = new CmdLineParser();

    /**
     * The single instance of this class.
     */
    private static SuraqOptions instance;

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
        Option smtfileOption = cmdLineParser.addStringOption('s', "smtfile");
        Option verboseOption = cmdLineParser.addBooleanOption('v', "verbose");

        try {
            cmdLineParser.parse(args);
        } catch (OptionException exc) {
            throw new SuraqException("Error in parsing options.", exc);
        }

        inputValue = (String) cmdLineParser.getOptionValue(inputOption);
        verboseValue = (Boolean) cmdLineParser.getOptionValue(verboseOption);
        smtfileValue = (String) cmdLineParser.getOptionValue(smtfileOption);

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
     * Returns the value of the input option.
     * 
     * @return the value of the input option.
     */
    public String getInput() {
        return inputValue != null ? inputValue : SuraqOptions.inputDefault;
    }

    /**
     * Returns the value of the smtfile option.
     * 
     * @return the value of the smtfile option.
     */
    public String getSmtfile() {
        return smtfileValue != null ? smtfileValue
                : SuraqOptions.smtfileDefault;
    }
}
