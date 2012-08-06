package at.iaik.suraq.main;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import at.iaik.suraq.util.DebugHelper;
import at.iaik.suraq.util.ProcessResult;
import at.iaik.suraq.util.ProcessUtil;

public class VeriTSolver {
    private static boolean isActive = false;

    public static final int NOT_RUN = 0;
    public static final int UNSAT = 1;
    public static final int SAT = 2;
    public static final int UNKNOWN = -1;

    private int state = VeriTSolver.NOT_RUN;

    private String path = "./lib/veriT/veriT";
    private File lastFile = null;

    public VeriTSolver() {

    }

    public void solve(String smt2) {
        if (!isActive) {
            System.err
                    .println("VeriTSolver didn't perform, because it was set inactive!");
            return;
        }
        DebugHelper.getInstance().stringtoFile(smt2, "debug_before-verit.txt");
        
        if (smt2.indexOf("(get-proof)") != -1) {
            System.err.println("Unsupported elements in smt2: (get-proof)");
        }
        File tmpOutFile;
        try {
            tmpOutFile = File.createTempFile("veriT-out", ".smt2");
            System.out.println("Temporary file: "+tmpOutFile);
        } catch (IOException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }

        String executionPath = path //
                + " --proof-version=1" // 0|1
                + " --proof=" + tmpOutFile // temporary file
                + " --proof-with-sharing" //
                + " --proof-prune" //
                + " --input=smtlib2" //
                + " --output=smtlib2" //
                //+ " --disable-print-success" // 
                + " --disable-banner" //
                // + " --max-time=SECONDS" // max. execution time in seconds
                // + " --disable-ackermann" // maybe?
        ;

        System.out.println("starting veriT: " + path);

        ProcessResult pResult = ProcessUtil.runExternalProcess(executionPath,
                smt2);
        System.out.println("i'm back from veriT...");

        String output = pResult.getOutputStream();
        String[] lines = output.split("\n");
        // StringBuffer proofBuffer = new StringBuffer();

        for (String line : lines) {
            if (line.equalsIgnoreCase("success")) {
                System.out.print(".");
                continue;
            } else if (line.equalsIgnoreCase("unsupported")) {
                System.out.print("-");
                continue;
            } 
            else if (line.equalsIgnoreCase("sat")) {
                state = QBFSolver.SAT;
                System.out.println("\nVeriT/SAT");
                break;
            } else if (line.equalsIgnoreCase("unsat")) {
                state = QBFSolver.UNSAT;
                System.out.println("\nVeriT/UNSAT");
                break;
            }

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
        //ProcessUtil.runExternalProcess("gedit " + tmpOutFile);
        
        if(tmpOutFile.exists())
        {
            lastFile = tmpOutFile;
        }
    }
    
    public BufferedReader getStream() throws FileNotFoundException {
        if (lastFile != null) {
            return new BufferedReader(new FileReader(lastFile));
        }
        throw new FileNotFoundException(
                "You may not have called VeriTSolver::solve() first.");
    }

    public int getState() {
        return state;
    }
    
    public static boolean isActive() {
        return VeriTSolver.isActive;
    }

    public static void setActive(boolean _isActive) {
        VeriTSolver.isActive = _isActive;
    }

}
