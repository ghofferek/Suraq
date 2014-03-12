/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.main;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.FunctionMacro;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;

/**
 * Helps encoding a Formula to QBF-Format
 * 
 * @author chillebold
 * 
 */
public class QBFEncoder {

    private static boolean _isActive = false;

    /**
     * Optional comment for QBF-Inputfile
     */
    private String comment = null;

    /**
     * Number of variables
     */
    protected int varcounter = 1;

    /**
     * Number of clauses (lines in QBF)
     */
    protected int clauses = 0;

    /**
     * cache for the unique variable-integer replacements
     */
    protected final Map<String, Integer> mapping = new HashMap<String, Integer>();

    /**
     * Empty public constructor
     */
    public QBFEncoder() {
        //
    }

    // List<PropositionalVariable> controlSignals =
    // logicParser.getControlVariables()
    public String encode(Formula formula, Set<Token> noDependenceVars,
            List<PropositionalVariable> controlSignals,
            Set<PropositionalVariable> tseitinEncoding) {
        // see http://www.qbflib.org/qdimacs.html for format
        mapping.clear();

        clauses = 0;
        varcounter = 1;
        StringBuilder sb = new StringBuilder();

        // check if the formula is in CNF
        if (!checkFormulaReady(formula))
            throw new RuntimeException(
                    "Formula not ready for QBF Encoding (AND).");

        AndFormula top = (AndFormula) formula;
        for (Formula innerFormula : top.getConjuncts()) {
            if (!(innerFormula instanceof OrFormula))
                throw new RuntimeException(
                        "Formula not ready for QBF Encoding (OR).");
            OrFormula inner = (OrFormula) innerFormula;

            for (Formula disjunctElem : inner.getDisjuncts()) {
                boolean not = disjunctElem instanceof NotFormula;
                Formula var = (disjunctElem instanceof NotFormula) ? ((NotFormula) disjunctElem)
                        .getNegatedFormula() : disjunctElem;
                if (var == null || !(var instanceof PropositionalVariable))
                    throw new RuntimeException(
                            "Formula not ready for QBF Encoding (PropVar/Not).");

                PropositionalVariable prop = (PropositionalVariable) var;
                int varID = encodeVar(prop.getVarName());
                if (not) // negative values for negated vars
                    varID *= -1;
                sb = sb.append(varID + " ");
            }
            sb = sb.append("0\n");
            clauses++;
        }

        StringBuilder header = makeQuantors(formula, noDependenceVars,
                controlSignals, tseitinEncoding);
        return header.append(sb.toString()).toString();
    }

    /**
     * generates the quantors and returns a StringBuilder
     * 
     * @param formula
     * @param noDependenceVars
     * @param controlSignals
     * @param tseitinEncoding
     * @return
     */
    protected StringBuilder makeQuantors(Formula formula,
            Set<Token> noDependenceVars,
            List<PropositionalVariable> controlSignals,
            Set<PropositionalVariable> tseitinEncoding) {
        // A ... for all
        // E ... exists
        // A inputs E control A no_dependence E tseitin
        // Assumption:
        // inputs is everything that is not control, no_dependence, tseitin

        StringBuilder header = new StringBuilder();
        if (comment != null)
            header = header.append("c " + comment + "\n");
        header = header.append("p cnf " + (varcounter - 1) + " " + clauses
                + "\n");

        // input vars
        Set<PropositionalVariable> inputVars = new HashSet<PropositionalVariable>();
        formula.getPropositionalVariables(inputVars,
                new HashSet<SMTLibObject>());
        inputVars.removeAll(controlSignals);
        inputVars.removeAll(tseitinEncoding);
        header = header.append("a ");
        for (PropositionalVariable var : inputVars) {
            if (!noDependenceVars.contains(Token.generate(var.getVarName())))
                header = header.append(encodeVar(var.getVarName()) + " ");
        }
        header = header.append("0\n");

        // control signals
        header = header.append("e ");
        for (PropositionalVariable var : controlSignals) {
            header = header.append(encodeVar(var.getVarName()) + " ");
        }
        header = header.append("0\n");

        // no dependence vars
        header = header.append("a ");
        for (Token var : noDependenceVars) {
            header = header.append(encodeVar(var.toString()) + " ");
        }
        header = header.append("0\n");

        // no dependence vars
        header = header.append("e ");
        for (PropositionalVariable var : tseitinEncoding) {
            header = header.append(encodeVar(var.getVarName()) + " ");
        }
        header = header.append("0\n");

        return header;
    }

    /**
     * returns an unique Integer replacement for each variable
     * 
     * @param varname
     * @return
     */
    protected Integer encodeVar(String varname) {
        if (mapping.containsKey(varname)) {
            return mapping.get(varname);
        }
        int varID = varcounter++;
        mapping.put(varname, varID);
        return varID;
    }

    /**
     * Checks if the given Formula does not contain any Arrays, DomainVariables,
     * FunctionMacros, UF and if the first layer formula is an AndFormula
     * 
     * @param formula
     * @return
     */
    public boolean checkFormulaReady(Formula formula) {
        if (!QBFEncoder._isActive) {
            System.err.println("QBFEncoder: QBFEncoder is inactive!");
            return false;
        }
        Set<ArrayVariable> arrayVars = new HashSet<ArrayVariable>();
        formula.getArrayVariables(arrayVars, new HashSet<SMTLibObject>());
        if (!arrayVars.isEmpty()) {
            System.err.println("QBFEncoder: There are Arrays in the Formula!");
            return false;
        }
        Set<DomainVariable> domainVars = new HashSet<DomainVariable>();
        formula.getDomainVariables(domainVars, new HashSet<SMTLibObject>());
        if (!domainVars.isEmpty()) {
            System.err
                    .println("QBFEncoder: There are DomainVariables in the Formula!");
            return false;
        }
        Set<FunctionMacro> macros = new HashSet<FunctionMacro>();
        formula.getFunctionMacros(macros, new HashSet<SMTLibObject>());
        if (!macros.isEmpty()) {
            System.err
                    .println("QBFEncoder: There are FunctionMacros in the Formula!");
            return false;
        }
        Set<UninterpretedFunction> ufs = new HashSet<UninterpretedFunction>();
        formula.getUninterpretedFunctions(ufs, new HashSet<SMTLibObject>());
        if (!ufs.isEmpty()) {
            System.err
                    .println("QBFEncoder: There are UninterpretedFunctions in the Formula!");
            return false;
        }
        if (!(formula instanceof AndFormula)) {
            System.err.println("QBFEncoder: The Formula must be in CNF!");
            System.err.println("The Formula is type of " + formula.getClass());
            return false;
        }
        return true;
    }

    public static void setActive(boolean isActive) {
        QBFEncoder._isActive = isActive;
    }

    public static boolean isActive() {
        return QBFEncoder._isActive;
    }

    public String getComment() {
        return comment;
    }

    /**
     * You can also set null if you don't want comments
     * 
     * @param comment
     */
    public void setComment(String comment) {
        this.comment = comment;
    }
}
