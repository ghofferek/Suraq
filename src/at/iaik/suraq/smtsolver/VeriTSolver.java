/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.smtsolver;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import at.iaik.suraq.main.SuraqOptions;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.util.DebugHelper;
import at.iaik.suraq.util.ProcessResult;
import at.iaik.suraq.util.ProcessUtil;
import at.iaik.suraq.util.Util;

/**
 * Connection to the VeriTSolver in the path ./lib/veriT/veriT. You can get the
 * State by calling ::getState() (NOT_RUN, UNSAT, SAT, UNKNOWN). This Class is
 * by default ACTIVE, but you can disable it by calling
 * VeriTSolver.setActive(false) . You may wish to modify the parameters for the
 * VeriTSolver in method ::solve(String smt2). It would be possible to connect
 * the veriT-Process by pipes, but for larger files the "pipe broke". In the
 * current implementation a UNIQUE temporary input and output file is created.
 * 
 * @author chillebold
 * 
 */
public class VeriTSolver extends SMTSolver {
    /**
     * Defines whether the method .solve(..) shall do anything or not (true =
     * active)
     */
    private static boolean isActive = true;

    /**
     * The Path of the executable veriT
     */
    private static String path = "./lib/veriT/veriT79dde157745ac50765678565c9f76894b8e8bf8b";

    /**
     * The Path of the VeriT-Proof File, if it exists.
     */
    private File lastFile = null;

    /**
     * The Path of the VeriT-Proof File (internal). This is also set if an error
     * occured.
     */
    private File proofFile = null;

    /**
     * Empty Constructor
     */
    public VeriTSolver() {
        //
    }

    /**
     * Writes the given smt2-String in a temporary File in the "./"-Directory.
     * 
     * @param smt2
     */
    @Override
    @Deprecated
    public void solve(String smt2) {
        // reset these variables
        lastFile = null;
        state = SMTSolver.NOT_RUN;

        if (!VeriTSolver.isActive) {
            System.err
                    .println("VeriTSolver didn't perform, because it was set inactive!");
            return;
        }
        DebugHelper.getInstance().stringtoFile(smt2, "debug_before-verit.txt");

        if (smt2.indexOf("(get-proof)") != -1) {
            System.err.println("Unsupported elements in smt2: (get-proof)");
        }
        File tmpInFile;
        try {
            // in the following code, a temporary file in the root directory of
            // the project is created.
            // TODO: You may want to change the folder or overwrite the old
            // files.
            // To overwrite just call the constructor of File instead of
            // createTempFile...
            proofFile = File.createTempFile("veriT-proof", ".smt2", new File(
                    "./"));
            if (!SuraqOptions.getInstance().getKeepTemFiles())
                proofFile.deleteOnExit();
            tmpInFile = File
                    .createTempFile("veriT-in", ".smt2", new File("./"));
            if (!SuraqOptions.getInstance().getKeepTemFiles())
                tmpInFile.deleteOnExit();
            FileWriter fw = new FileWriter(tmpInFile);
            fw.write(smt2);
            fw.close();
            System.out.println("Temporary Out file: " + proofFile);
            System.out.println("Temporary In  file: " + tmpInFile);
        } catch (IOException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }

        String executionPath = VeriTSolver.path //
                + " --proof-version=1" // 0|1
                + " --proof=" + proofFile // temporary file
                + " --proof-with-sharing" //
                + " --proof-prune" //
                + " --proof-merge" //
                + " --input=smtlib2" //
                + " --output=smtlib2" //
                + " --disable-print-success" //
                + " --disable-banner" //
                // + " --max-time=SECONDS" // max. execution time in seconds
                // + " --disable-ackermann" // maybe?
                + " " + tmpInFile;

        Util.printToSystemOutWithWallClockTimePrefix("starting veriT: "
                + executionPath);

        // ProcessResult pResult = ProcessUtil.runExternalProcess(executionPath,
        // smt2);
        ProcessResult pResult = ProcessUtil.runExternalProcess(executionPath,
                "");
        Util.printToSystemOutWithWallClockTimePrefix("veriT is done.");

        String output = pResult.getOutputStream();
        String[] lines = output.split("\n");
        // StringBuffer proofBuffer = new StringBuffer();

        // parse the lines of the output:
        for (String line : lines) {
            if (line.equalsIgnoreCase("success")) {
                // System.out.print(".");
                continue;
            } else if (line.equalsIgnoreCase("unsupported")) {
                System.out.print("-");
                continue;
            } else if (line.equalsIgnoreCase("sat")) {
                state = SMTSolver.SAT;
                System.out.println("\nVeriT/SAT");
                continue;
            } else if (line.equalsIgnoreCase("unsat")) {
                state = SMTSolver.UNSAT;
                System.out.println("\nVeriT/UNSAT");
                continue;
            }

            // for pipes this would be working:
            // if (!line.equals("success") && !line.equals("sat") &&
            // !line.equals("unsat")) {
            // proofBuffer.append(line + "\n");
            // }
        }

        if (state == SMTSolver.NOT_RUN)
            state = SMTSolver.UNKNOWN;

        if (pResult.getExitCode() != 0) {
            System.out.println("EXIT CODE: " + pResult.getExitCode());
            System.out.println("ERROR:     " + pResult.getErrorStream());
            System.out.println("OUTPUT:    " + output);
        }

        // Code to view the proof (gedit required)
        // ProcessUtil.runExternalProcess("gedit " + tmpOutFile);

        if (proofFile.exists()) {
            lastFile = proofFile;
        }
    }

    /**
     * @see at.iaik.suraq.smtsolver.SMTSolver#solve(java.io.File)
     */
    @Override
    public void solve(File file) {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtsolver.SMTSolver#solve(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public void solve(Formula formula) {
        List<Formula> formulas = new ArrayList<Formula>(1);
        formulas.add(formula);
        solve(formulas);
    }

    /**
     * @see at.iaik.suraq.smtsolver.SMTSolver#solve(at.iaik.suraq.smtlib.formula.Formula)
     */
    public void solve(Collection<? extends Formula> formulas) {
        // reset these variables
        lastFile = null;
        state = SMTSolver.NOT_RUN;

        if (!VeriTSolver.isActive) {
            System.err
                    .println("VeriTSolver didn't perform, because it was set inactive!");
            return;
        }

        File tmpInFile;
        try {
            // in the following code, a temporary file in the root directory of
            // the project is created.
            // TODO: You may want to change the folder or overwrite the old
            // files.
            // To overwrite just call the constructor of File instead of
            // createTempFile...
            proofFile = File.createTempFile("veriT-proof", ".smt2", new File(
                    "./"));
            tmpInFile = File
                    .createTempFile("veriT-in", ".smt2", new File("./"));
            if (!SuraqOptions.getInstance().getKeepTemFiles())
                tmpInFile.deleteOnExit();
            FileWriter fw = new FileWriter(tmpInFile);
            BufferedWriter writer = new BufferedWriter(fw);
            writer.write(SExpressionConstants.SET_LOGIC_QF_UF.toString());
            writer.write("\n");
            writer.write(SExpressionConstants.DECLARE_SORT_VALUE.toString());
            writer.write("\n");
            AndFormula conjunction = AndFormula
                    .generate(new ArrayList<Formula>(formulas));
            Util.writeDeclarations(conjunction, writer);
            for (Formula formula : formulas) {
                writer.write("(" + SExpressionConstants.ASSERT.toString() + " ");
                formula.writeTo(writer);
                writer.write(" )\n");
            }
            writer.write(SExpressionConstants.CHECK_SAT.toString());
            writer.write(SExpressionConstants.EXIT.toString());
            writer.close();
            fw.close();
            System.out.println("Temporary Out file: " + proofFile);
            System.out.println("Temporary In  file: " + tmpInFile);
        } catch (IOException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }

        String executionPath = VeriTSolver.path //
                + " --proof-version=1" // 0|1
                + " --proof=" + proofFile // temporary file
                + " --proof-with-sharing" //
                + " --proof-prune" //
                + " --proof-merge" //
                + " --input=smtlib2" //
                + " --output=smtlib2" //
                + " --disable-print-success" //
                + " --disable-banner" //
                // + " --max-time=SECONDS" // max. execution time in seconds
                // + " --disable-ackermann" // maybe?
                + " " + tmpInFile;

        Util.printToSystemOutWithWallClockTimePrefix("starting veriT: "
                + executionPath);

        // ProcessResult pResult = ProcessUtil.runExternalProcess(executionPath,
        // smt2);
        ProcessResult pResult = ProcessUtil.runExternalProcess(executionPath,
                "");
        Util.printToSystemOutWithWallClockTimePrefix("veriT is done.");

        String output = pResult.getOutputStream();
        String[] lines = output.split("\n");
        // StringBuffer proofBuffer = new StringBuffer();

        // parse the lines of the output:
        for (String line : lines) {
            if (line.equalsIgnoreCase("success")) {
                // System.out.print(".");
                continue;
            } else if (line.equalsIgnoreCase("unsupported")) {
                System.out.print("-");
                continue;
            } else if (line.equalsIgnoreCase("sat")) {
                state = SMTSolver.SAT;
                System.out.println("\nVeriT/SAT");
                continue;
            } else if (line.equalsIgnoreCase("unsat")) {
                state = SMTSolver.UNSAT;
                System.out.println("\nVeriT/UNSAT");
                continue;
            }

            // for pipes this would be working:
            // if (!line.equals("success") && !line.equals("sat") &&
            // !line.equals("unsat")) {
            // proofBuffer.append(line + "\n");
            // }
        }

        if (state == SMTSolver.NOT_RUN)
            state = SMTSolver.UNKNOWN;

        if (pResult.getExitCode() != 0) {
            System.out.println("EXIT CODE: " + pResult.getExitCode());
            System.out.println("ERROR:     " + pResult.getErrorStream());
            System.out.println("OUTPUT:    " + output);
        }

        // Code to view the proof (gedit required)
        // ProcessUtil.runExternalProcess("gedit " + tmpOutFile);

        if (proofFile.exists()) {
            lastFile = proofFile;
        }

    }

    /**
     * Solves the given <code>dimacsFile</code>
     * 
     * @param dimacsFile
     * @throws IOException
     */
    public void solveDimacs(File dimacsFile) throws IOException {

        proofFile = File.createTempFile("veriT-proof-dimacs", ".smt2",
                new File("./"));
        if (!SuraqOptions.getInstance().getKeepTemFiles())
            proofFile.deleteOnExit();
        String executionPath = VeriTSolver.path //
                + " --proof-version=1" // 0|1
                + " --proof=" + proofFile // temporary file
                + " --proof-with-sharing" //
                + " --proof-prune" //
                + " --proof-merge" //
                + " --input=dimacs" //
                + " --output=smtlib2" //
                + " --disable-print-success" //
                + " --disable-banner" //
                // + " --max-time=SECONDS" // max. execution time in seconds
                // + " --disable-ackermann" // maybe?
                + " " + dimacsFile;

        Util.printToSystemOutWithWallClockTimePrefix("starting veriT: "
                + executionPath);

        // ProcessResult pResult = ProcessUtil.runExternalProcess(executionPath,
        // smt2);
        ProcessResult pResult = ProcessUtil.runExternalProcess(executionPath,
                "");
        Util.printToSystemOutWithWallClockTimePrefix("veriT is done.");

        String output = pResult.getOutputStream();
        String[] lines = output.split("\n");
        // StringBuffer proofBuffer = new StringBuffer();

        // parse the lines of the output:
        for (String line : lines) {
            if (line.equalsIgnoreCase("success")) {
                // System.out.print(".");
                continue;
            } else if (line.equalsIgnoreCase("unsupported")) {
                System.out.print("-");
                continue;
            } else if (line.equalsIgnoreCase("sat")) {
                state = SMTSolver.SAT;
                System.out.println("\nVeriT/SAT");
                continue;
            } else if (line.equalsIgnoreCase("unsat")) {
                state = SMTSolver.UNSAT;
                System.out.println("\nVeriT/UNSAT");
                continue;
            }
        }

        if (pResult.getExitCode() != 0) {
            System.out.println("EXIT CODE: " + pResult.getExitCode());
            System.out.println("ERROR:     " + pResult.getErrorStream());
            System.out.println("OUTPUT:    " + output);
        }

        if (proofFile.exists()) {
            lastFile = proofFile;
        }

    }

    /**
     * Reads the Proof-File and returns a BufferedReader. If the method
     * solve(...) did not perform successfully, this method can throw a
     * FileNotFoundException.
     * 
     * @return
     * @throws FileNotFoundException
     */
    public BufferedReader getStream() throws FileNotFoundException {
        if (lastFile != null) {
            return new BufferedReader(new FileReader(lastFile));
        }
        throw new FileNotFoundException(
                "You may not have called VeriTSolver::solve() first.");
    }

    /**
     * Returns the Result of the VeriTProof.
     * 
     * @return a constant of VeriTSolver (NOT_RUN, UNSAT, SAT, UNKNOWN)
     */
    @Override
    public int getState() {
        return state;
    }

    /**
     * Returns whether this Class shall be active or not.
     * 
     * @return
     */
    public static boolean isActive() {
        return VeriTSolver.isActive;
    }

    /**
     * You can disable the .solve(..) method of this class by calling
     * .setActive(false)
     * 
     * @param _isActive
     *            true if the .solve(..) method should do anything
     */
    public static void setActive(boolean _isActive) {
        VeriTSolver.isActive = _isActive;
    }

    /**
     * Returns the Path of the VeriT-Proof-File
     * 
     * @return Path of the VeriT-Proof-File
     */
    public String getProofFile() {
        return proofFile.getPath();
    }

}
