/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.main;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.formula.AndFormula;
import at.iaik.suraq.formula.DomainTerm;
import at.iaik.suraq.formula.DomainVariable;
import at.iaik.suraq.formula.Formula;
import at.iaik.suraq.formula.FunctionMacro;
import at.iaik.suraq.formula.PropositionalConstant;
import at.iaik.suraq.formula.PropositionalVariable;
import at.iaik.suraq.formula.Term;
import at.iaik.suraq.formula.UninterpretedFunction;
import at.iaik.suraq.parser.LogicParser;
import at.iaik.suraq.parser.SExpParser;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
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
     * The expression that will be written to the output.
     */
    private SExpression outputExpression;

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
    private Map<Token, Token> varTypes;

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

    /**
     * @see java.lang.Runnable#run()
     */
    @Override
    public void run() {

        printWelcome();

        SuraqOptions options = SuraqOptions.getInstance();

        File sourceFile = new File(options.getInput());
        if (options.isVerbose())
            System.out.println("Parsing input file " + sourceFile.toString());
        SExpParser sExpParser = null;
        try {
            sExpParser = new SExpParser(sourceFile);
        } catch (FileNotFoundException exc) {
            System.err.println("ERROR: File " + sourceFile.getPath()
                    + " not found!");
            return;
        } catch (IOException exc) {
            System.err.println("ERROR: Could not read from file "
                    + sourceFile.getPath());
            return;
        }

        try {
            sExpParser.parse();
            assert (sExpParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            return;
        }

        logicParser = new LogicParser(sExpParser.getRootExpr());

        try {
            logicParser.parse();
            assert (logicParser.wasParsingSuccessfull());
        } catch (ParseError exc) {
            handleParseError(exc);
            return;
        }
        // Parsing complete
        if (options.isVerbose())
            System.out.println("Parsing completed successfully!");

        boolean noErrors = true;

        try {
            doMainWork();
            File smtfile = new File(options.getSmtfile());
            FileWriter fstream = new FileWriter(smtfile);
            BufferedWriter smtfilewriter = new BufferedWriter(fstream);
            smtfilewriter.write(outputExpression.toString());
            smtfilewriter.close();
        } catch (SuraqException exc) {
            noErrors = false;
            if (exc.getMessage() != null)
                System.out.println(exc.getMessage());
        } catch (IOException exc) {
            System.err.println("Error while writing to smtfile.");
            exc.printStackTrace();
        }

        // All done :-)
        printEnd(noErrors);
        return;
    }

    /**
     * Performs the main work.
     * 
     * @throws SuraqException
     *             if something goes wrong
     */
    private void doMainWork() throws SuraqException {

        Formula formula = logicParser.getMainFormula().deepFormulaCopy();
        Set<Token> noDependenceVars = new HashSet<Token>(
                logicParser.getNoDependenceVariables());

        Set<Formula> constraints = new HashSet<Formula>();
        formula.removeArrayWrites(formula, constraints, noDependenceVars);
        constraints.add(formula);
        formula = new AndFormula(constraints);

        formula.removeArrayEqualities();

        Set<DomainTerm> indexSet = formula.getIndexSet();
        lambda = new DomainVariable(Util.freshVarName(formula, "lambda"));
        indexSet.add(lambda);
        noDependenceVars.add(new Token(lambda.getVarName()));
        formula.arrayPropertiesToFiniteConjunctions(indexSet);

        formula.arrayReadsToUninterpretedFunctions(noDependenceVars);

        List<PropositionalVariable> controlSignals = logicParser
                .getControlVariables();

        if (controlSignals.size() > 30) {
            throw new SuraqException(
                    "Current implementation cannot handle more than 30 control signals.");
        }

        outputExpression = new SExpression();
        outputExpression.addChild(new SExpression(
                SExpressionConstants.SET_LOGIC_QF_UF));
        outputExpression.addChild(new SExpression(
                SExpressionConstants.SET_OPTION_PRODUCE_INTERPOLANT));
        outputExpression.addChild(new SExpression(
                SExpressionConstants.DECLARE_SORT_VALUE));

        writeDeclarationsAndDefinitions(formula, noDependenceVars,
                controlSignals.size());

        writeAssertPartitions(formula, noDependenceVars, controlSignals);

        outputExpression.addChild(SExpressionConstants.CHECK_SAT);

        outputExpression.addChild(SExpressionConstants.EXIT);

    }

    /**
     * Writes the assert-partitions for the expanded formula to the
     * <code>outputExpression</code>.
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

        if (outputExpression == null)
            throw new SuraqException("outputExpression not initialized!");

        for (int count = 0; count < (1 << controlSignals.size()); count++) {
            Formula tempFormula = formula.deepFormulaCopy();
            Map<Token, Term> variableSubstitutions = new HashMap<Token, Term>();
            for (Token var : noDependenceVars) {
                if (noDependenceFunctionsCopies.containsKey(var))
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
                                    + "is neither a variabel nor an uninterpreted function.");
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

            SExpression assertPartitionExpression = new SExpression();
            assertPartitionExpression
                    .addChild(SExpressionConstants.ASSERT_PARTITION);
            assertPartitionExpression.addChild(tempFormula.toSmtlibV2());
            outputExpression.addChild(assertPartitionExpression);
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

        if (outputExpression == null)
            throw new SuraqException("outputExpression not initialized!");

        varTypes = new HashMap<Token, Token>();
        Map<Token, Integer> functionArity = new HashMap<Token, Integer>();

        for (PropositionalVariable var : formula.getPropositionalVariables()) {
            if (noDependenceVars.contains(var.toSmtlibV2())) {
                varTypes.put(new Token(var.getVarName()),
                        SExpressionConstants.BOOL_TYPE);
                continue; // noDependenceVars will be handled later.
            }
            outputExpression
                    .addChild(SExpression.makeDeclareFun(
                            (Token) var.toSmtlibV2(),
                            SExpressionConstants.BOOL_TYPE, 0));
        }

        for (DomainVariable var : formula.getDomainVariables()) {
            if (noDependenceVars.contains(var.toSmtlibV2())) {
                varTypes.put(new Token(var.getVarName()),
                        SExpressionConstants.VALUE_TYPE);
                continue; // noDependenceVars will be handled later.
            }
            outputExpression.addChild(SExpression.makeDeclareFun(
                    (Token) var.toSmtlibV2(), SExpressionConstants.VALUE_TYPE,
                    0));
        }

        for (UninterpretedFunction function : formula
                .getUninterpretedFunctions()) {
            if (noDependenceVars.contains(function.getName())) {
                varTypes.put(new Token(function.getType()),
                        SExpressionConstants.VALUE_TYPE);
                functionArity.put(function.getName(), function.getNumParams());
                continue; // noDependenceVars will be handled later.
            }
            outputExpression.addChild(SExpression.makeDeclareFun(
                    function.getName(), SExpressionConstants.VALUE_TYPE,
                    function.getNumParams()));
        }

        // Now dealing with noDependenceVars
        noDependenceVarsCopies = new HashMap<Token, List<Term>>();
        for (Token var : noDependenceVars) {
            Token type = varTypes.get(var);
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

            for (int count = 0; count < (1 << numControlSignals); count++) {
                String name = Util.freshVarName(formula, var.toString()
                        + "_copy_" + count);
                outputExpression.addChild(SExpression.makeDeclareFun(new Token(
                        name), type, numParams));
                if (numParams == 0) {
                    if (type.equals(SExpressionConstants.BOOL_TYPE))
                        listOfVarCopies.add(new PropositionalVariable(name));
                    else
                        listOfVarCopies.add(new DomainVariable(name));
                } else {
                    listOfFunctionCopies.add(new UninterpretedFunction(name,
                            numParams, type));
                }
            }
        }

        for (FunctionMacro macro : formula.getFunctionMacros())
            outputExpression.addChild(macro.toSmtlibV2());
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
