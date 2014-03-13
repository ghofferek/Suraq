/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */

package at.iaik.suraq.smtsolver;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.util.ProcessResult;
import at.iaik.suraq.util.ProcessResultStreams;
import at.iaik.suraq.util.ProcessUtil;
import at.iaik.suraq.util.Util;

/**
 * SMT-solver bindings for the Microsoft(TM) Z3 solver. Utilizes external calls
 * to Z3 application and parses Z3 output.
 * 
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
public class z3 extends SMTSolver {

    /**
     * Stores the path to the Z3 distribution.
     */
    private String z3Path;

    /**
     * Constructs a new <code>z3</code> SMT-solver with the given base-path.
     * 
     * @param solverBasePath
     *            base-path to the Z3 distribution.
     */
    public z3(String solverBasePath) {
        z3Path = solverBasePath;
    }

    /**
     * @see at.iaik.suraq.smtsolver.SMTSolver#solveStr(String)
     */
    @Override
    @Deprecated
    public void solve(String smtStr) {
        String executionPath = z3Path;

        if (System.getProperty("os.name").toLowerCase().contains("windows"))
            executionPath = executionPath.concat(" /smt2 /in");
        else
            executionPath = executionPath.concat(" -smt2 -in");

        ProcessResult pResult = ProcessUtil.runExternalProcess(executionPath,
                smtStr);

        String[] lines = pResult.getOutputStream().split("\n");
        StringBuffer proofBuffer = new StringBuffer();

        for (String line : lines) {
            if (!line.equals("success") && !line.equals("sat")
                    && !line.equals("unsat")) {
                proofBuffer.append(line + "\n");
            }
            if (line.equals("sat"))
                state = SMTSolver.SAT;
            else if (line.equals("unsat"))
                state = SMTSolver.UNSAT;
        }

        if (state == SMTSolver.NOT_RUN)
            state = SMTSolver.UNKNOWN;

        if (state == SMTSolver.UNSAT)
            this.proof = proofBuffer.toString();

        if (pResult.getExitCode() != 0) {
            System.out.println("EXIT CODE: " + pResult.getExitCode());
            System.out.println("ERROR from Z3:" + pResult.getErrorStream());
            System.out.println("OUTPUT from Z3: " + pResult.getOutputStream());
        }
    }

    /**
     * @see at.iaik.suraq.smtsolver.SMTSolver#solve(java.io.File)
     */
    @Override
    public void solve(File file) {
        String executionPath = z3Path;
        if (System.getProperty("os.name").toLowerCase().contains("windows"))
            executionPath = executionPath.concat(" /smt2 /file:"
                    + file.toString());
        else
            executionPath = executionPath.concat(" -smt2 -file:"
                    + file.toString());

        ProcessResult pResult = ProcessUtil.runExternalProcess(executionPath,
                "");

        String[] lines = pResult.getOutputStream().split("\n");
        StringBuffer proofBuffer = new StringBuffer();

        for (String line : lines) {
            if (!line.equals("success") && !line.equals("sat")
                    && !line.equals("unsat")) {
                proofBuffer.append(line + "\n");
            }
            if (line.equals("sat"))
                state = SMTSolver.SAT;
            else if (line.equals("unsat"))
                state = SMTSolver.UNSAT;
        }

        if (state == SMTSolver.NOT_RUN)
            state = SMTSolver.UNKNOWN;

        if (state == SMTSolver.UNSAT)
            this.proof = proofBuffer.toString();

        if (pResult.getExitCode() != 0) {
            System.out.println("EXIT CODE: " + pResult.getExitCode());
            System.out.println("ERROR from Z3:" + pResult.getErrorStream());
            System.out.println("OUTPUT from Z3: " + pResult.getOutputStream());
        }

    }

    /**
     * @see at.iaik.suraq.smtsolver.SMTSolver#solve2(String)
     */
    public String solve2(String smtStr) {
        String executionPath = z3Path;
        if (System.getProperty("os.name").toLowerCase().contains("windows"))
            executionPath = executionPath.concat(" /smt2 /in");
        else
            executionPath = executionPath.concat(" -smt2 -in");

        ProcessResult pResult = ProcessUtil.runExternalProcess(executionPath,
                smtStr);

        if (pResult.getExitCode() != 0) {
            System.out.println("EXIT CODE: " + pResult.getExitCode());
            System.out.println("ERROR from Z3: " + pResult.getErrorStream());
            System.out.println("OUTPUT from Z3: " + pResult.getOutputStream());

        }
        return pResult.getOutputStream();
    }

    /**
     * Simplified the given formula.
     * 
     * @param formula
     * @return a reader with the output of the solver.
     */
    public BufferedReader simplify(Formula formula) {
        File tmpInFile = null;
        try {
            // in the following code, a temporary file in the root directory of
            // the project is created.
            // TODO: You may want to change the folder or overwrite the old
            // files.
            // To overwrite just call the constructor of File instead of
            // createTempFile...

            tmpInFile = File.createTempFile("z3-in-simplify", ".smt2",
                    new File("./"));
            FileWriter fw = new FileWriter(tmpInFile);
            BufferedWriter writer = new BufferedWriter(fw);
            writer.write(SExpressionConstants.SET_LOGIC_QF_UF.toString());
            writer.write("\n");
            writer.write(SExpressionConstants.DECLARE_SORT_VALUE.toString());
            writer.write("\n");
            Util.writeDeclarations(formula, writer);
            writer.write("(" + SExpressionConstants.SIMPLIFY.toString() + " ");
            formula.writeTo(writer);
            writer.write(" " + SExpressionConstants.ELIM_AND.toString() + " "
                    + SExpressionConstants.TRUE + ")\n");
            writer.write(SExpressionConstants.EXIT.toString());
            writer.close();
            fw.close();
            System.out.println("Temporary z3 file: " + tmpInFile);
        } catch (IOException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
        assert (tmpInFile != null);
        String executionPath = z3Path;
        if (System.getProperty("os.name").toLowerCase().contains("windows"))
            executionPath += " /smt2 /file:" + tmpInFile.toString();
        else
            executionPath += " -smt2 -file:" + tmpInFile.toString();

        ProcessResultStreams pResult = ProcessUtil
                .runExternalProcessWithStreamResult(executionPath);

        if (pResult.getExitCode() != 0) {

            System.out.println("EXIT CODE: " + pResult.getExitCode());
            System.out.println("ERROR from Z3:");
            String line;
            try {
                while ((line = pResult.getErrorStream().readLine()) != null)
                    System.out.println(line);
                System.out.println();
                System.out.println("OUTPUT from Z3:");
                while ((line = pResult.getOutputStream().readLine()) != null)
                    System.out.println(line);
            } catch (IOException exc) {
                System.out
                        .println("IOException while trying to display Z3 output.");
                throw new RuntimeException(exc);
            }

        }
        return pResult.getOutputStream();

    }

    /**
     * @see at.iaik.suraq.smtsolver.SMTSolver#solve(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public void solve(Formula formula) {
        File tmpInFile = null;
        try {
            // in the following code, a temporary file in the root directory of
            // the project is created.
            // TODO: You may want to change the folder or overwrite the old
            // files.
            // To overwrite just call the constructor of File instead of
            // createTempFile...

            tmpInFile = File.createTempFile("z3-in-solve", ".smt2", new File(
                    "./"));
            FileWriter fw = new FileWriter(tmpInFile);
            BufferedWriter writer = new BufferedWriter(fw);
            writer.write(SExpressionConstants.SET_LOGIC_QF_UF.toString());
            writer.write("\n");
            writer.write(SExpressionConstants.DECLARE_SORT_VALUE.toString());
            writer.write("\n");
            Util.writeDeclarations(formula, writer);
            writer.write("(" + SExpressionConstants.ASSERT.toString() + " ");
            formula.writeTo(writer);
            writer.write(" )\n");
            writer.write(SExpressionConstants.CHECK_SAT.toString());
            writer.write(SExpressionConstants.EXIT.toString());
            writer.close();
            fw.close();
            System.out.println("Temporary z3 file: " + tmpInFile);
        } catch (IOException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
        assert (tmpInFile != null);
        String executionPath = z3Path;
        if (System.getProperty("os.name").toLowerCase().contains("windows"))
            executionPath += " /smt2 /file:" + tmpInFile.toString();
        else
            executionPath += " -smt2 -file:" + tmpInFile.toString();

        ProcessResultStreams pResult = ProcessUtil
                .runExternalProcessWithStreamResult(executionPath);

        if (pResult.getExitCode() != 0) {

            System.out.println("EXIT CODE: " + pResult.getExitCode());
            System.out.println("ERROR from Z3:");
            String line;
            try {
                while ((line = pResult.getErrorStream().readLine()) != null)
                    System.out.println(line);
                System.out.println();
                System.out.println("OUTPUT from Z3:");
                while ((line = pResult.getOutputStream().readLine()) != null)
                    System.out.println(line);
            } catch (IOException exc) {
                System.out
                        .println("IOException while trying to display Z3 output.");
                throw new RuntimeException(exc);
            }

        }
        String line;
        try {
            while ((line = pResult.getOutputStream().readLine()) != null) {

                if (line.equals("sat"))
                    state = SMTSolver.SAT;
                else if (line.equals("unsat"))
                    state = SMTSolver.UNSAT;
            }
        } catch (IOException exc) {
            throw new RuntimeException("IOException while reading z3 output",
                    exc);
        }

        if (state == SMTSolver.NOT_RUN)
            state = SMTSolver.UNKNOWN;
    }

}
