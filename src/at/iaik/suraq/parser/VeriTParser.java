/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.parser;

import java.io.BufferedReader;
import java.io.IOException;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import at.iaik.suraq.exceptions.IncomparableTermsException;
import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.exceptions.WrongFunctionTypeException;
import at.iaik.suraq.exceptions.WrongNumberOfParametersException;
import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.proof.VeriTToken;
import at.iaik.suraq.proof.VeritProof;
import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.resProof.ResProof;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.util.ImmutableSet;
import at.iaik.suraq.util.Util;

public class VeriTParser extends Parser {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private final BufferedReader reader;

    /**
     * two macro buffers: for Formulas and Terms
     */
    private final HashMap<String, Formula> macroBufferFormula = new HashMap<String, Formula>();
    private final HashMap<String, Term> macroBufferTerm = new HashMap<String, Term>();

    // The constructor stores the objects in these functions.
    // Therefore we know, which type they are.
    private final Set<PropositionalVariable> propositionalVariables;
    private final Set<DomainVariable> domainVariables;
    private final Set<String> uninterpretedFunctionNames;
    private final Set<UninterpretedFunction> uninterpretedFunctions;

    /**
     * Finally the Proof is stored here.
     */
    private final VeritProof proof = new VeritProof();

    // Stacks are used to store variables of several Layers
    // a Layer is opened, when a ( occurs, and closed on )

    /**
     * name of the macro, which is currently being defined
     */
    private final Stack<String> macroNameStack = new Stack<String>();

    /**
     * name of the command of the current Stack (and, or, =)
     */
    private final Stack<String> commandStack = new Stack<String>();

    /**
     * list of formulas of every stack, content of command
     */
    private final Stack<ArrayList<Formula>> formulaStack = new Stack<ArrayList<Formula>>();

    /**
     * list of terms of every stack, content of command
     */
    private final Stack<ArrayList<Term>> termStack = new Stack<ArrayList<Term>>();

    /**
     * the UninterpretedFunction defined on the current stack
     */
    private final Stack<UninterpretedFunction> uninterpretedStack = new Stack<UninterpretedFunction>();

    /**
     * the current line for debug output or Exceptions
     */
    private int currentLine = 0;

    /**
     * The ResProof. If not null, we parse into this ResProof instead of into a
     * veriT proof.
     */
    private ResProof resProof = null;

    /**
     * Map from literal IDs to partitions
     */
    private Map<Integer, Integer> partitions = null;

    /**
     * Map from clauses of leaves to partitions
     */
    private Map<ImmutableSet<Integer>, Integer> leafPartitions = null;

    /**
     * The VeriTParser needs all those Parameters to know which variable had
     * which type. The current version will not work if two UF have the same
     * name but an other count of parameters. In that case, please rename the
     * function.
     * 
     * @param reader
     *            a BufferedReader to Parse; it will be parsed line by line
     * @param oldTopLevelFormula
     *            we extract variables etc. out of this
     * @param tseitinVars
     * @param noDependenceVarsCopies
     * @param noDependenceFunctionsCopies
     */
    public VeriTParser(BufferedReader reader, Formula oldTopLevelFormula,
            Set<PropositionalVariable> tseitinVars,
            Collection<List<Term>> noDependenceVarsCopies,
            Map<Token, List<UninterpretedFunction>> noDependenceFunctionsCopies) {
        assert (reader != null);
        this.reader = reader;

        // extract all variables out of the old Formula
        this.domainVariables = oldTopLevelFormula.getDomainVariables();
        this.propositionalVariables = oldTopLevelFormula
                .getPropositionalVariables();
        this.uninterpretedFunctionNames = oldTopLevelFormula
                .getUninterpretedFunctionNames();
        this.uninterpretedFunctions = oldTopLevelFormula
                .getUninterpretedFunctions();

        // add the tseitinVars
        propositionalVariables.addAll(tseitinVars);

        // look for noDependenceVarsCopies (DomainVariable,
        // PropositionalVariable)
        for (List<Term> terms : noDependenceVarsCopies) {
            for (Term term : terms) {
                if (term instanceof DomainVariable)
                    this.domainVariables.add((DomainVariable) term);
                else if (term instanceof PropositionalVariable)
                    this.propositionalVariables
                            .add((PropositionalVariable) term);
                else if (term instanceof ArrayVariable)
                    throw new RuntimeException(
                            "Didn't expect array variables here.");
                else
                    throw new RuntimeException(
                            "Unknown type of noDependenceVarCopies");
            }
        }

        // look for noDependenceFunctionCopies (UF, UP)
        for (List<UninterpretedFunction> ufs : noDependenceFunctionsCopies
                .values()) {
            for (UninterpretedFunction uf : ufs) {
                uninterpretedFunctions.add(uf);
                uninterpretedFunctionNames.add(uf.getName().toString());
            }
        }
    }

    /**
     * Constructs a new <code>VeriTParser</code>.
     * 
     * @param stream
     * @param inverseLiteralIds
     * @param resProof
     */
    public VeriTParser(BufferedReader stream, int maxId, ResProof resProof,
            Map<Integer, Integer> partitions,
            Map<ImmutableSet<Integer>, Integer> leafPartitions) {
        this.uninterpretedFunctionNames = new HashSet<String>();
        this.uninterpretedFunctions = new HashSet<UninterpretedFunction>();
        this.domainVariables = new HashSet<DomainVariable>();
        this.reader = stream;
        this.propositionalVariables = new HashSet<PropositionalVariable>(
                2 * maxId);
        for (int count = 1; count <= maxId; count++)
            this.propositionalVariables.add(PropositionalVariable.create("v_"
                    + Integer.toString(count)));
        this.partitions = new HashMap<Integer, Integer>(partitions);
        this.leafPartitions = new HashMap<ImmutableSet<Integer>, Integer>(
                leafPartitions);
    }

    private void cleanUp() {
        try {
            reader.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        macroBufferFormula.clear();
        macroBufferTerm.clear();
        propositionalVariables.clear();
        domainVariables.clear();
        uninterpretedFunctionNames.clear();
        uninterpretedFunctions.clear();

        macroNameStack.clear();
        commandStack.clear();
        formulaStack.clear();
        termStack.clear();
        uninterpretedStack.clear();
    }

    /**
     * Parses the Proof line by line. Formula Expressions in the proof are
     * parsed in the method parseConclusion(...)
     */
    @Override
    public void parse() {
        try {
            String line = reader.readLine();
            while (line != null) {
                currentLine++; // count the lines

                line = line.trim();
                if (line.length() == 0) {
                    line = reader.readLine();
                    continue;
                }

                if (currentLine % 10000 == 0) {
                    Util.printToSystemOutWithWallClockTimePrefix("  Now starting to parse line "
                            + Util.largeNumberFormatter.format(currentLine));
                    VeritProofNode.printCheckCountersAndTimers();
                }
                if (currentLine % 100000 == 0) {
                    Util.printMemoryInformation();
                }

                // every line has to start with (set .
                if (!line.startsWith("(set "))
                    throw new ParseError(currentLine, line);

                // Extract the name of the ProofNode
                int pos_begin = "(set ".length();
                int pos_end = line.indexOf(' ', pos_begin);
                String name = line.substring(pos_begin, pos_end);

                // extract the content of the ProofNode as 'rest'
                // rest = (input :conclusion (#1:(and (not #2:(= lambda_....))
                // excl. surrounding brackets
                String rest = line.substring(pos_end + 2, line.length() - 1);

                // Extract the type of the ProofNode
                pos_end = rest.indexOf(' ', 0);
                // input,and, or,resolution, eq_transitive,...
                // you may add more types in VeriTToken
                Token type = VeriTToken.parse(rest.substring(0, pos_end));

                // find :clauses, :iargs and :conclusion if exists
                int pos_clauses = rest.indexOf(":clauses ", 0);
                int pos_iargs = rest.indexOf(":iargs ", 0);
                int pos_conclusion = rest.indexOf(":conclusion ", 0);

                // prepare parsing them
                String clauses = null;
                String[] parsed_clauses = null;
                String iargs = null;
                Integer parsed_iargs = null;
                ArrayList<VeritProofNode> parsed_clauses2 = null;
                ArrayList<Formula> conclusions = null;

                // if :clauses exists, parse them
                if (pos_clauses > 0) {
                    // the range of the :clauses depends on if a :iargs if found
                    // after
                    int until = (pos_iargs > 0) ? pos_iargs : pos_conclusion;
                    // find the clauses and split them by whitespaces
                    clauses = rest.substring(
                            pos_clauses + ":clauses (".length(), until - 2);
                    // REGEX: \s=A whitespace character: [ \t\n\x0B\f\r]
                    parsed_clauses = clauses.split("\\s");
                    // find the given clauses in already existing ProofNodes and
                    if (resProof == null) {
                        parsed_clauses2 = new ArrayList<VeritProofNode>();
                        for (String parsed_clause : parsed_clauses) {
                            VeritProofNode proofNode = proof
                                    .getProofNode(parsed_clause);
                            assert (proofNode != null);
                            parsed_clauses2.add(proofNode);
                        }
                    }

                }

                // if :iargs exists, parse them
                if (pos_iargs > 0) {
                    iargs = rest.substring(pos_iargs + ":iargs (".length(),
                            pos_conclusion - 2);
                    parsed_iargs = Integer.parseInt(iargs);
                }

                // parse :conclusion
                // parse conclusion WITH brackets, because they are needed by
                // the parseConclusion(..)-Formula-Parser
                String conclusion = rest.substring(pos_conclusion
                        + ":conclusion ".length(), rest.length() - 1);

                if (conclusion.length() == 0)
                    conclusion = null;
                else
                    conclusions = parseConclusion(conclusion);

                // System.out.println("Parsed Conclusions: "+
                // conclusions.toString());
                // DebugHelper.getInstance().stringtoFile(conclusions.toString(),
                // "~verit_z"+lines+".tmp");

                // Store the ProofNode to the Proof
                assert (conclusions != null);
                if (resProof == null) {
                    proof.addProofNode(name, type, conclusions,
                            parsed_clauses2, parsed_iargs, !SuraqOptions
                                    .getInstance()
                                    .getDontRemoveLemmaSubproofs());
                } else {
                    assert (partitions != null);
                    assert (leafPartitions != null);
                    resProof.add(name, type, conclusions, parsed_clauses,
                            partitions, leafPartitions);
                }

                // read next line
                line = reader.readLine();
            }
            parsingSuccessfull = true;

        } catch (Exception e) {
            parsingSuccessfull = false;
            System.err.println("Error parsing line " + currentLine);
            e.printStackTrace();
            throw new RuntimeException(e);
        } finally {
            System.out.println("There were " + currentLine + " lines.");
            cleanUp();
        }
    }

    /**
     * This is a non-iterative (sequential) attempt to parse a Formula. This is
     * done to reduce the stack and to improve performance. Although the code is
     * more complicated and not that easy to understand.
     * 
     * The formula can consist of And, Or, Equivalences, Not,
     * PropositionalVariables, DomainVariables, UninterpretedFunctions and
     * UninterpretedPredicates. It supports definitions of Function in the Form
     * #1:(...). These definitions can be used by writing #1.
     * 
     * @param conclusion
     *            the Formula to Parse
     * @param lineNumber
     *            LineNumber, used when an Exception is thrown
     * @return
     * @throws ParseException
     * @throws IncomparableTermsException
     */
    private ArrayList<Formula> parseConclusion(String conclusion)
            throws ParseException, IncomparableTermsException {
        try {
            // caches the length of the formula to parse
            int length = conclusion.length();
            // store all conclusions on the TopLayer of the Formula
            ArrayList<Formula> conclusions = new ArrayList<Formula>();
            // if this flag is set, we are currently parsing a macro_name:
            // -> the number between # and :)
            boolean macro_name = false;
            // a StringBuilder to store the current variable name
            StringBuilder str = new StringBuilder();

            // iterate each character
            for (int i = 0; i < length; i++) {
                char cur = conclusion.charAt(i);

                // is this the end of a variable?
                if (cur == ' ' || cur == ')') {
                    // was this a macro_name? e.g. #12 or #12)
                    if (macro_name) {
                        // find a pre-defined formula, that was #12
                        Formula formula = macroBufferFormula
                                .get(str.toString());
                        Term term = macroBufferTerm.get(str.toString());
                        if (formula != null) {
                            formulaStack.peek().add(formula);
                        }
                        if (term != null) {
                            termStack.peek().add(term);
                        }
                        // we didn't find the macro
                        if (term == null && formula == null) {
                            throw new ParseException("Macro #" + str
                                    + " was not declared before (line="
                                    + currentLine + ").", currentLine);
                        }
                        macro_name = false;
                    }
                    // it is a variable/UF/UP or a command
                    else {
                        String tmp = str.toString();
                        // is it a command? and, or, =
                        if (tmp.equals("and") || tmp.equals("or")
                                || tmp.equals("=") || tmp.equals("not")) {
                            commandStack.pop();
                            commandStack.push(tmp);
                        }
                        // is it a variable/UF/UP?
                        else if (tmp.length() > 0) {
                            if (uninterpretedFunctionNames.contains(tmp)) {
                                // its an uninterpreted function, save it
                                uninterpretedStack.pop();
                                uninterpretedStack
                                        .push(findUninterpretedFunction(tmp));
                            } else {
                                // its a variable
                                Term term = findVariable(tmp);
                                if (term instanceof PropositionalVariable)
                                    formulaStack.peek().add(
                                            (PropositionalVariable) term);
                                // DomainVariable and PropositionalVariable
                                termStack.peek().add(term);
                            }
                        }
                    }
                }
                if (cur == ' ') {
                    // variable end handled above
                }
                // we got an opening bracket
                else if (cur == '(') {
                    // extend all Stacks and init them with null or a List
                    formulaStack.push(new ArrayList<Formula>());
                    termStack.push(new ArrayList<Term>());
                    commandStack.push(null);
                    macroNameStack.push(null);
                    uninterpretedStack.push(null);
                }
                // we got a closing bracket
                else if (cur == ')') {
                    // find out if this shall be stored to a macro:
                    String macroname = null;
                    macroNameStack.pop();
                    if (macroNameStack.size() != 0) // stack could be empty
                        macroname = macroNameStack.peek();

                    // get the command
                    String command = commandStack.pop();

                    // find out if there was an UF/UP
                    UninterpretedFunction uf = uninterpretedStack.pop();
                    if (uf != null) {
                        // pops the termStack and the formulaStack
                        this.parseUF(uf, macroname);
                    }
                    // we got a closing bracket, and it is no UF/UP
                    else {
                        // we must have a command for each stack except the
                        // first
                        if (command != null) {
                            // pops and peeks the formulaStack and the termStack
                            this.parseCommand(command);

                            // store macro if this was a macro
                            if (macroname != null) {
                                this.storeMacro(macroname, formulaStack.peek()
                                        .get(formulaStack.peek().size() - 1));
                            }
                        }
                        // just a list of variables
                        else {
                            ArrayList<Formula> formulaElements = formulaStack
                                    .pop();
                            if (commandStack.size() == 0) {
                                // this is the :conclusion layer
                                conclusions.addAll(formulaElements);
                            } else {
                                throw new ParseException(
                                        "We have a list of Variables without command.",
                                        currentLine);
                            }
                        }
                    }
                }
                // this is the beginning of a macro-definition #2:
                // or a beginning of a macro-usage: #2
                else if (cur == '#') {
                    macro_name = true;
                }
                // this is the end of a macro-definition (name)
                else if (cur == ':') {
                    macro_name = false;
                    // store the macroname, so it can be stored when a closing
                    // bracket is found
                    macroNameStack.pop();
                    macroNameStack.push(str.toString());
                }
                // a normal character
                else {
                    str.append(cur);
                    continue;
                }
                // clear the buffer:
                str.setLength(0);
            }
            return conclusions;
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * parses an UninterpretedFunction
     * 
     * @param uf
     *            the Uninterpreted Function to parse
     * @param macroname
     *            null or the name of the UF, how it is stored
     * @throws WrongNumberOfParametersException
     * @throws WrongFunctionTypeException
     */
    private void parseUF(UninterpretedFunction uf, String macroname)
            throws WrongNumberOfParametersException, WrongFunctionTypeException {
        // generate a new UninterpretedFunctionInstance or
        // UninterpretedPredicateInstance
        // with the parameters stored in formulaElements
        ArrayList<DomainTerm> formulaElements = new ArrayList<DomainTerm>();
        for (Term tmp3 : termStack.pop())
            formulaElements.add((DomainTerm) tmp3);
        formulaStack.pop();

        Term newTerm = null;
        if (uf.getType().equalsString("Value")) {
            newTerm = UninterpretedFunctionInstance.create(uf, formulaElements);

            if (macroname != null) {
                // System.out.println("[M] Stored macro #" + macroname);
                macroBufferTerm.put(macroname, newTerm);
            }
        } else if (uf.getType().equalsString("Bool")) {
            newTerm = UninterpretedPredicateInstance
                    .create(uf, formulaElements);
            // additionally add to formulaStack
            formulaStack.peek().add((UninterpretedPredicateInstance) newTerm);

            if (macroname != null) {
                // System.out.println("[M] Stored macro #" + macroname);
                macroBufferFormula.put(macroname,
                        (UninterpretedPredicateInstance) newTerm);
                macroBufferTerm.put(macroname, newTerm);
            }
        } else
            assert (false);
        // add UF/UP to termStack
        termStack.peek().add(newTerm);
    }

    /**
     * Parses a command/expression/? (=, and, or, not)
     * 
     * @param command
     *            one of ["=", "and", "or", "not"]
     * @throws ParseException
     * @throws IncomparableTermsException
     */
    private void parseCommand(String command) throws ParseException,
            IncomparableTermsException {
        ArrayList<Formula> formulaElements = formulaStack.pop();
        ArrayList<Term> termElements = termStack.pop();
        if (command.equals("not")) {
            if (formulaElements.size() != 1)
                throw new ParseException("Not has not 1 element. #Elements="
                        + formulaElements.size(), currentLine);
            formulaStack.peek().add(NotFormula.create(formulaElements.get(0)));
        } else if (command.equals("=")) {
            formulaStack.peek().add(EqualityFormula.create(termElements, true));
        } else if (command.equals("and")) {
            formulaStack.peek().add(AndFormula.generate(formulaElements));
        } else if (command.equals("or")) {
            formulaStack.peek().add(OrFormula.generate(formulaElements));
        } else {
            throw new ParseException("Unknown Command", currentLine);
        }
    }

    /**
     * Stores a Macro to the Buffer
     * 
     * @param macroName
     *            name of the Macro
     * @param formula
     *            Formula, by which the macro is defined
     */
    private void storeMacro(String macroName, Formula formula) {
        // System.out.println("[M] Stored macro #" + macroName);
        macroBufferFormula.put(macroName, formula);
        if (formula instanceof Term)
            macroBufferTerm.put(macroName, (Term) formula);
    }

    /**
     * finds an UninterpretedFunction by searching in the already existing
     * variables.
     * 
     * @param name
     * @return
     */
    private UninterpretedFunction findUninterpretedFunction(String name) {
        if (this.uninterpretedFunctionNames.contains(name)) {
            UninterpretedFunction uf = null;
            for (UninterpretedFunction tmp : uninterpretedFunctions) {
                // NOTE: please do not use the same name for different count of
                // parameters or different types
                if (tmp.getName().equalsString(name)) {
                    uf = UninterpretedFunction.create(tmp.getName(),
                            tmp.getNumParams(), tmp.getType());
                    break;
                }
            }
            if (uf != null)
                return uf;
        }
        String err = "Unknown Variable '"
                + name
                + "' on parsing. Cannot decide if it is a propositional or domain variable.";
        System.err.println(err);
        throw new RuntimeException(err);
    }

    /**
     * find a variable in the already given variables
     * 
     * @param name
     *            name of the variable
     * @return
     */
    private Term findVariable(String name) {
        if (this.domainVariables.contains(DomainVariable.create(name))) {
            return DomainVariable.create(name);
        } else if (this.propositionalVariables.contains(PropositionalVariable
                .create(name))) {
            return PropositionalVariable.create(name);
        }
        String err = "Unknown Variable '"
                + name
                + "' on parsing. Cannot decide if it is a propositional or domain variable.";
        System.err.println(err);
        throw new RuntimeException(err);
    }

    /**
     * Returns the finally parsed Proof as a VeriTProof.
     * 
     * @return
     */
    public VeritProof getProof() {
        return proof;
    }

}
