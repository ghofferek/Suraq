/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */

package at.iaik.suraq.smtsolver;

import at.iaik.suraq.util.ProcessResult;
import at.iaik.suraq.util.ProcessUtil;

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
        }
    }

    /**
     * @see at.iaik.suraq.smtsolver.SMTSolver#tseitin_encode(String)
     */
    @Override
    public String tseitin_encode(String smtStr) {
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
        }
        return pResult.getOutputStream();
    }
}
