/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */

package at.iaik.suraq.smtsolver;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

/**
 * SMT-solver bindings for the Microsoft(TM) Z3 solver. Utilizes external calls
 * to Z3 application and parses Z3 output.
 * 
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
public class z3 extends SMTSolver {

    /**
     * Stores the base-path to the Z3 distribution.
     */
    private String basePath;

    /**
     * Constant containing the multi-threaded binary directory of Z3.
     */
    private static final String mtBinPath = "bin_mt/";

    /**
     * Constant containing the single-threaded binary directory of Z3.
     */
    private static final String binPath = "bin/";

    /**
     * Constant containing the binary name of Z3.
     */
    private static final String binary = "z3.exe";

    /**
     * State of multi-threading support.
     */
    private boolean mtEnabled = false;

    /**
     * Constructs a new <code>z3</code> SMT-solver with the given base-path.
     * 
     * @param solverBasePath
     *            base-path to the Z3 distribution.
     */
    public z3(String solverBasePath) {
        basePath = solverBasePath;
    }

    /**
     * @see at.iaik.suraq.smtsolver.SMTSolver#enableMultiThreaded()
     */
    @Override
    protected void enableMultiThreaded() {
        mtEnabled = true;
    }

    /**
     * @see at.iaik.suraq.smtsolver.SMTSolver#solve(String)
     */
    @Override
    public void solve(String filename) {
        // TODO: <bk> add proper error checking + handling

        System.out.println("checking file: " + filename);

        String executionPath = basePath;
        if (mtEnabled)
            executionPath = executionPath.concat(z3.mtBinPath);
        else
            executionPath = executionPath.concat(z3.binPath);

        executionPath = executionPath.concat(z3.binary);
        executionPath = executionPath.concat(" /smt2 " + filename);

        try {
            Process p = Runtime.getRuntime().exec(executionPath);

            BufferedReader input = new BufferedReader(new InputStreamReader(
                    p.getInputStream()));
            BufferedReader error = new BufferedReader(new InputStreamReader(
                    p.getErrorStream()));

            String line;
            StringBuffer proofBuffer = new StringBuffer();

            while ((line = input.readLine()) != null) {
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

            int exitCode = p.exitValue();

            System.out.println("EXIT CODE: " + exitCode);

            System.out.println("ERROR from Z3:");
            while ((line = error.readLine()) != null) {
                System.out.println("   " + line);
            }

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * @see at.iaik.suraq.smtsolver.SMTSolver#solveStr(String)
     */
    @Override
    public void solveStr(String smtStr) {
        String executionPath = basePath;
        if (mtEnabled)
            executionPath = executionPath.concat(z3.mtBinPath);
        else
            executionPath = executionPath.concat(z3.binPath);

        executionPath = executionPath.concat(z3.binary);
        executionPath = executionPath.concat(" /smt2 /in");

        try {
            Process p = Runtime.getRuntime().exec(executionPath);

            BufferedWriter output = new BufferedWriter(new OutputStreamWriter(
                    p.getOutputStream()));
            BufferedReader input = new BufferedReader(new InputStreamReader(
                    p.getInputStream()));
            BufferedReader error = new BufferedReader(new InputStreamReader(
                    p.getErrorStream()));

            output.write(smtStr);
            output.flush();
            output.close();

            String line;
            StringBuffer proofBuffer = new StringBuffer();

            while ((line = input.readLine()) != null) {
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

            int exitCode = p.exitValue();

            System.out.println("EXIT CODE: " + exitCode);

            System.out.println("ERROR from Z3:");
            while ((line = error.readLine()) != null) {
                System.out.println("   " + line);
            }

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * @see at.iaik.suraq.smtsolver.SMTSolver#simplify(String)
     */
    @Override
    public String simplify(String smtStr) {
        String executionPath = basePath;
        if (mtEnabled)
            executionPath = executionPath.concat(z3.mtBinPath);
        else
            executionPath = executionPath.concat(z3.binPath);

        executionPath = executionPath.concat(z3.binary);
        executionPath = executionPath.concat(" /smt2 /in");
        StringBuffer resultBuffer = new StringBuffer();

        try {
            Process p = Runtime.getRuntime().exec(executionPath);

            BufferedWriter output = new BufferedWriter(new OutputStreamWriter(
                    p.getOutputStream()));
            BufferedReader input = new BufferedReader(new InputStreamReader(
                    p.getInputStream()));
            BufferedReader error = new BufferedReader(new InputStreamReader(
                    p.getErrorStream()));

            output.write(smtStr);
            output.flush();
            output.close();

            String line;

            line = input.readLine();
            while (line != null && !line.trim().equals("--EOF--")) {
                if (!line.equals("success") && !line.equals("sat")
                        && !line.equals("unsat")) {
                    resultBuffer.append(line + "\n");
                }
                line = input.readLine();
            }

            int exitCode = p.exitValue();

            System.out.println("EXIT CODE: " + exitCode);
            System.out.println("ERROR from Z3:");
            while ((line = error.readLine()) != null) {
                System.out.println("   " + line);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }

        return resultBuffer.toString();
    }
}
