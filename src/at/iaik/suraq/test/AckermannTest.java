package at.iaik.suraq.test;

import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.main.Ackermann;
import at.iaik.suraq.main.Suraq;
import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.parser.LogicParser;
import at.iaik.suraq.parser.SExpParser;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.FunctionMacro;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtsolver.SMTSolver;

/**
 * This class tests if the Ackermann's reduction works.
 * It is not possible to perform all tests, only:
 * * the given formula is unsatisfiable
 * * the given formula is valid
 * @author chillebold
 *
 */
public class AckermannTest {
	//SuraqOptions options;
	protected Formula consequent;
	public AckermannTest()
	{
		//options = SuraqOptions.getInstance();
	}
	
	@Before
	public void setUp() {
	    SuraqOptions.kill();
	    SuraqOptions.reset();
	    Z3Proof.setInstanceCounter(0);
	}

	
	// Live: Ständig zum Herumprobieren
	@Test
	public void liveTest() {  
        System.out.println("****************************************************");
        System.out.println("Testcase: Live: "+"./rsc/test/live.smt2");
		boolean result = testFile("./rsc/test/live.smt2", "./rsc/test/live-acker.smt2", "./rsc/test/live-unsat.smt2");
		System.out.println("  live: " + (result?"Success :-)":"Failed :-("));
	    Assert.assertTrue(result);
	}
	

	// Ackermann Example aus dem Buch: 3.4 auf Seite 66 - normal
	@Test
	public void example0Test() {
        System.out.println("****************************************************");
        System.out.println("Testcase: Example 3.4 (pg. 66): "+"./rsc/test/ex34.smt2");
		boolean result = testFile("./rsc/test/ex34.smt2", "./rsc/test/ex34-acker.smt2", "./rsc/test/ex34-unsat.smt2");
		System.out.println("  Example 3.4 (pg. 66): " + (result?"Success :-)":"Failed :-("));
	    Assert.assertTrue(result);
	}


	// Ackermann Example aus dem Buch: 3.4 auf Seite 66 - mit AND statt OR ganz außen.
	@Test
	public void example1Test() {  
        System.out.println("****************************************************");
        System.out.println("Testcase: Unsatisfiable with one function: "+"./rsc/test/a01.smt2");
		boolean result = testFile("./rsc/test/a01.smt2", "./rsc/test/a01-acker.smt2", "./rsc/test/a01-unsat.smt2");
		System.out.println("  Example 3.4 (pg. 66) mit AND statt OR: " + (result?"Success :-)":"Failed :-("));
	    Assert.assertTrue(result);
	}

	// Bsp erweitert um eine zusätzliche Funktion
	@Test
	public void twoFunctions() { 
	    System.out.println("****************************************************");
        System.out.println("Testcase: 2 different Functions, unsatisfiable: "+ "./rsc/test/a02.smt2");
		boolean result = testFile("./rsc/test/a02.smt2", "./rsc/test/a02-acker.smt2", "./rsc/test/a02-unsat.smt2");
		System.out.println("  2 Functions: " + (result?"Success :-)":"Failed :-("));
	    Assert.assertTrue(result);
	}
	

    // Bsp erweitert um eine zusätzliche Funktion
    @Test
    public void recursiveFunctions() { 
        System.out.println("****************************************************");
        System.out.println("Testcase: 2 different Functions, recursively, valid: "+ "./rsc/test/a03.smt2");
        boolean result = testFile("./rsc/test/a03.smt2", "./rsc/test/a03-acker.smt2", "./rsc/test/a03-unsat.smt2");
        System.out.println("  2 Functions recursively: " + (result?"Success :-)":"Failed :-("));
        Assert.assertTrue(result);
    }
	

    // Bsp erweitert um eine zusätzliche Funktion
    @Test
    public void largerRecursiveFunctions() { 
        System.out.println("****************************************************");
        System.out.println("Testcase: larger recursive functions, valid: "+ "./rsc/test/a04.smt2");
        boolean result = testFile("./rsc/test/a04.smt2", "./rsc/test/a04-acker.smt2", "./rsc/test/a04-unsat.smt2");
        System.out.println("  larger recursive functions: " + (result?"Success :-)":"Failed :-("));
        Assert.assertTrue(result);
    }

    // Bsp erweitert um eine zusätzliche Funktion
    @Test
    public void twoParameters() { 
        System.out.println("****************************************************");
        System.out.println("Testcase: two Parameters, valid: "+ "./rsc/test/a05.smt2");
        boolean result = testFile("./rsc/test/a05.smt2", "./rsc/test/a05-acker.smt2", "./rsc/test/a05-unsat.smt2");
        System.out.println("  2 Parameters: " + (result?"Success :-)":"Failed :-("));
        Assert.assertTrue(result);
    }
    

    // Bsp erweitert um eine zusätzliche Funktion
    @Test
    public void threeParametersWithInnerFunction() { 
        System.out.println("****************************************************");
        System.out.println("Testcase: three Parameters with inner function, valid: "+ "./rsc/test/a06.smt2");
        boolean result = testFile("./rsc/test/a06.smt2", "./rsc/test/a06-acker.smt2", "./rsc/test/a06-unsat.smt2");
        System.out.println("  three Parameters with inner function: " + (result?"Success :-)":"Failed :-("));
        Assert.assertTrue(result);
    }

    // Bsp erweitert um eine zusätzliche Funktion
    @Test
    public void functionParameterOrderTest() { 
        System.out.println("****************************************************");
        System.out.println("Testcase: testing correct order of parameters, valid: "+ "./rsc/test/a07.smt2");
        boolean result = testFile("./rsc/test/a07.smt2", "./rsc/test/a07-acker.smt2", "./rsc/test/a07-unsat.smt2");
        System.out.println("  testing correct order of parameters: " + (result?"Success :-)":"Failed :-("));
        Assert.assertTrue(result);
    }
    

    
    
	///////////////////////////////////////////////////////////////////////////////
	
	
	
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

        for (PropositionalVariable var : formula.getPropositionalVariables())
            outputExpressions
                    .add(SExpression.makeDeclareFun((Token) var.toSmtlibV2(),
                            SExpressionConstants.BOOL_TYPE, 0));

        for (DomainVariable var : formula.getDomainVariables())
            outputExpressions.add(SExpression.makeDeclareFun(
                    (Token) var.toSmtlibV2(), SExpressionConstants.VALUE_TYPE,
                    0));

        for (UninterpretedFunction function : formula
                .getUninterpretedFunctions())
            outputExpressions.add(SExpression.makeDeclareFun(
                    function.getName(), function.getType(),
                    function.getNumParams()));

        for (FunctionMacro macro : this.consequent.getFunctionMacros())
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
	
	
	protected Formula getFormulaOfFile(String filename)
	{
		File input = new File(filename);
		//String z3InputStr = inputTransformations(sourceFile);
		
		try{
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
		}catch(ParseError ex)
		{
			handleParseError(ex);
            throw new RuntimeException("Unable to parse proof!");
		}
		catch(Exception ex)
		{
            ex.printStackTrace();
            throw new RuntimeException("Other Exception");
		}
	}
	
	protected String transformFormulaToString(Formula mainFormula)
	{
		String declarationStr = makeDeclarationsAndDefinitions(mainFormula);
        String formulaSmtStr = buildSMTDescription(declarationStr,
        		mainFormula.toString());
        return formulaSmtStr;
	}
	
	protected void writeFile(String filename, String content)
	{
		try{
			File outputFile = new File(filename);
	        FileWriter fstream = new FileWriter(outputFile);
	        fstream.write(content);
	        fstream.close();
		}
		catch(Exception ex)
		{
			System.err.println("Datei konnte nicht geschrieben werden: "+ filename);
		}
	}
	
	protected boolean testFile(String filename, String outputFileName1, String outputFileName2)
	{
		Formula formula = getFormulaOfFile(filename);
        SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type,
                SuraqOptions.getZ3_4Path());
		
		if(formula == null)
		{
			System.err.println("formula == null");
			return false;
		}
		Formula old_formula = formula.deepFormulaCopy();
		
		// Ackermann
		Ackermann ack = new Ackermann();
		HashSet<Token> t = new HashSet<Token>();
		formula = ack.performAckermann(formula, t);
		
		//ArrayList<PropositionalTerm> col = new ArrayList();
		//col.add(old_formula.);
		
		// Debug output of Ackermann's result to Filesystem
		String ackermannstr = transformFormulaToString(formula);
		writeFile(outputFileName1, ackermannstr);
		
		Formula x = formula;
		
		z3.solve(transformFormulaToString(x));
		int state_acker = z3.getState();
		z3.solve(transformFormulaToString(formula));
		int state_old = z3.getState();
		if(state_acker == state_old)
		{
		    System.out.println("  Z3 tells us for before and after: "+state_old+" (1=sat, 2=unsat) ");
		}
		else
		{
            System.err.println("  Z3 tells us for before: "+state_old+" and after: "+state_acker+" (1=sat, 2=unsat) ");
		}
		
		//PropositionalEq equiv = new PropositionalEq(col, false); // false for inequality
		ImpliesFormula f1 = new ImpliesFormula(old_formula, x);
		ImpliesFormula f2 = new ImpliesFormula(x, old_formula);
		ArrayList<Formula> f12 = new ArrayList<Formula>();
		f12.add(f1);
		f12.add(f2);
		AndFormula equiv = new AndFormula(f12);
		
		NotFormula whole = new NotFormula(equiv);
		
		Formula toShow = whole;
		String z3InputStr = transformFormulaToString(toShow);
		
		writeFile(outputFileName2, z3InputStr);
        z3.solve(z3InputStr);

        switch (z3.getState()) {
        case SMTSolver.UNSAT:
            System.out.println("  Z3 tells us UNSAT. Good :-)");
            return true;
        case SMTSolver.SAT:
            System.err.println("  Z3 tells us SAT. Bad :-(");
            return false;
        default:
            System.err
                    .println("  Z3 OUTCOME ---->  UNKNOWN! CHECK ERROR STREAM.");
            throw (new RuntimeException(
                    "Z3 tells us UNKOWN STATE. CHECK ERROR STREAM."));
        }
	}
	

}
