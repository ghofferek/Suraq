package at.iaik.suraq.test;

import java.io.File;
import java.io.FileWriter;
import java.util.HashSet;
import java.util.Set;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.parser.LogicParser;
import at.iaik.suraq.parser.SExpParser;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.FunctionMacro;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtsolver.SMTSolver;

public class TestHelper {
    protected Formula consequent;

    public void setUp() {
        SuraqOptions.kill();
        SuraqOptions.reset();
        Z3Proof.setInstanceCounter(0);
    }

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

    protected String makeDeclarationsAndDefinitions(Formula formula) {

        Set<SExpression> outputExpressions = new HashSet<SExpression>();

        Set<SMTLibObject> done = new HashSet<SMTLibObject>();
        Set<PropositionalVariable> pVars = new HashSet<PropositionalVariable>();
        formula.getPropositionalVariables(pVars, done);
        done.clear();

        for (PropositionalVariable var : pVars)
            outputExpressions
                    .add(SExpression.makeDeclareFun((Token) var.toSmtlibV2(),
                            SExpressionConstants.BOOL_TYPE, 0));

        Set<DomainVariable> dVars = new HashSet<DomainVariable>();
        formula.getDomainVariables(dVars, done);
        done.clear();
        for (DomainVariable var : dVars)
            outputExpressions.add(SExpression.makeDeclareFun(
                    (Token) var.toSmtlibV2(), SExpressionConstants.VALUE_TYPE,
                    0));

        Set<UninterpretedFunction> ufs = new HashSet<UninterpretedFunction>();
        formula.getUninterpretedFunctions(ufs, done);
        done.clear();
        for (UninterpretedFunction function : ufs)
            outputExpressions.add(SExpression.makeDeclareFun(
                    function.getName(), function.getType(),
                    function.getNumParams()));

        Set<FunctionMacro> macros = new HashSet<FunctionMacro>();
        this.consequent.getFunctionMacros(macros, done);
        done.clear();
        for (FunctionMacro macro : macros)
            outputExpressions.add(macro.toSmtlibV2());

        String declarationsStr = "";
        for (SExpression declaration : outputExpressions)
            declarationsStr += declaration.toString();

        return declarationsStr;
    }

    protected String buildSMTDescription(String declarationStr,
            String formulaStr) {
        String smtStr = "";

        smtStr += SExpressionConstants.SET_LOGIC_QF_UF.toString();
        smtStr += SExpressionConstants.DECLARE_SORT_VALUE.toString();

        smtStr += declarationStr;

        smtStr += "(assert" + formulaStr + ")";

        smtStr += SExpressionConstants.CHECK_SAT.toString();
        smtStr += SExpressionConstants.EXIT.toString();

        return smtStr;
    }

    protected Formula getFormulaOfFile(String filename) {
        File input = new File(filename);
        // String z3InputStr = inputTransformations(sourceFile);

        try {
            SExpParser sExpParser = new SExpParser(input);

            try {
                sExpParser.parse();
                assert (sExpParser.wasParsingSuccessfull());
            } catch (ParseError exc) {
                handleParseError(exc);
                return null;
            }

            LogicParser logicParser = new LogicParser(sExpParser.getRootExpr());
            logicParser.parse();
            assert (logicParser.wasParsingSuccessfull());
            Formula mainFormula = logicParser.getMainFormula();
            Formula formula = mainFormula.flatten();
            consequent = formula;
            return formula;
        } catch (ParseError ex) {
            handleParseError(ex);
            throw new RuntimeException("Unable to parse proof!");
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException("Other Exception");
        }
    }

    protected String transformFormulaToString(Formula mainFormula) {
        String declarationStr = makeDeclarationsAndDefinitions(mainFormula);
        String formulaSmtStr = buildSMTDescription(declarationStr,
                mainFormula.toString());
        return formulaSmtStr;
    }

    protected void writeFile(String filename, String content) {
        try {
            File outputFile = new File(filename);
            FileWriter fstream = new FileWriter(outputFile);
            fstream.write(content);
            fstream.close();
        } catch (Exception ex) {
            System.err.println("Datei konnte nicht geschrieben werden: "
                    + filename);
        }
    }

    protected boolean isFormulaValid(Formula formula, String description) {
        this.setUp();
        SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type,
                SuraqOptions.getZ3_4Path());
        NotFormula valid = NotFormula.create(formula);
        z3.solve(transformFormulaToString(valid));
        int valid2 = z3.getState();
        if (valid2 == 1) // (1=UNSAT, 2=SAT)
        {
            System.out.println("Formula '" + description + "' is valid");
            return true;
        } else {
            System.out.println("Formula '" + description + "' is not valid");
            return false;
        }
    }

    protected boolean isFormulaSat(Formula formula, String description) {
        this.setUp();
        SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type,
                SuraqOptions.getZ3_4Path());
        z3.solve(transformFormulaToString(formula));
        int valid2 = z3.getState();
        if (valid2 == 1) // (1=UNSAT, 2=SAT)
        {
            System.out.println("Formula '" + description + "' is UNSAT");
            return false;
        } else {
            System.out.println("Formula '" + description + "' is SAT");
            return true;
        }
    }
}
