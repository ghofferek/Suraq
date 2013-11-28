/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.smtsolver;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

import at.iaik.suraq.main.QBFSolver;
import at.iaik.suraq.util.DebugHelper;
import at.iaik.suraq.util.ProcessResult;
import at.iaik.suraq.util.ProcessUtil;

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
public class VeriTSolver {
    /**
     * Defines whether the method .solve(..) shall do anything or not (true =
     * active)
     */
    private static boolean isActive = true;

    /**
     * The method .solve(..) and the VeriT-Solver did not return until now
     */
    public static final int NOT_RUN = 0;

    /**
     * The VeriTSolver says that the given SMT-String is UNSAT
     */
    public static final int UNSAT = 1;

    /**
     * The VeriTSolver says that the given SMT-String is SAT
     */
    public static final int SAT = 2;

    /**
     * The VeriTSolver didn't say if the given SMT-String is SAT or UNSAT. Maybe
     * there was an error on parsing or something unexpected.
     */
    public static final int UNKNOWN = -1;

    /**
     * The state of the Parser, by Default it is VeriTSolver.NOT_RUN
     */
    private int state = VeriTSolver.NOT_RUN;

    /**
     * The Path of the executable veriT
     */
    private String path = "./lib/veriT/veriT";

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
    public void solve(String smt2) {
        // reset these variables
        lastFile = null;
        state = VeriTSolver.NOT_RUN;

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
            tmpInFile = File
                    .createTempFile("veriT-in", ".smt2", new File("./"));
            FileWriter fw = new FileWriter(tmpInFile);
            fw.write(smt2);
            fw.close();
            System.out.println("Temporary Out file: " + proofFile);
            System.out.println("Temporary In  file: " + tmpInFile);
        } catch (IOException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }

        String executionPath = path //
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

        System.out.println("starting veriT: " + executionPath);

        // ProcessResult pResult = ProcessUtil.runExternalProcess(executionPath,
        // smt2);
        ProcessResult pResult = ProcessUtil.runExternalProcess(executionPath,
                "");
        System.out.println("i'm back from veriT...");

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
                state = QBFSolver.SAT;
                System.out.println("\nVeriT/SAT");
                continue;
            } else if (line.equalsIgnoreCase("unsat")) {
                state = QBFSolver.UNSAT;
                System.out.println("\nVeriT/UNSAT");
                continue;
            }

            // for pipes this would be working:
            // if (!line.equals("success") && !line.equals("sat") &&
            // !line.equals("unsat")) {
            // proofBuffer.append(line + "\n");
            // }
        }

        if (state == QBFSolver.NOT_RUN)
            state = QBFSolver.UNKNOWN;

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
