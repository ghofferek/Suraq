/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.main;

import at.iaik.suraq.util.ProcessResult;
import at.iaik.suraq.util.ProcessUtil;

/**
 * Interface to the QBF-Solver. It has 4 possible states: NOT_RUN, UNSAT, SAT,
 * UNKNOWN.
 * 
 * @author chillebold
 * 
 */
public class QBFSolver {
    private static boolean isActive = false;

    /**
     * The method .solve(..) and the QBFSolver did not return until now
     */
    public static final int NOT_RUN = 0;

    /**
     * The QBFSolver says that the given SMT-String is UNSAT
     */
    public static final int UNSAT = 1;

    /**
     * The QBFSolver says that the given SMT-String is SAT
     */
    public static final int SAT = 2;

    /**
     * The QBFSolver didn't say if the given SMT-String is SAT or UNSAT. Maybe
     * there was an error on parsing or something unexpected.
     */
    public static final int UNKNOWN = -1;

    /**
     * Where is the QBF-Solver located?
     */
    private String qbfPath = "./lib/tools/depqbf/depqbf";

    /**
     * This is the current state of the QBFSolver. By default it is
     * QBFSolver.NOT_RUN
     */
    private int state = QBFSolver.NOT_RUN;

    /**
     * Empty public constructor
     */
    public QBFSolver() {
    }

    /**
     * Calls the QBFSolver and gives it the given String. You can get the Result
     * of the QBFSolver by calling ::getState() after this method finished.
     * 
     * @param smtStr
     */
    public void solve(String smtStr) {
        String executionPath = qbfPath;

        System.out.println("starting external process...");
        // This may take very long, even for medium examples!
        ProcessResult pResult = ProcessUtil.runExternalProcess(executionPath,
                smtStr);
        System.out.println("i'm back...");

        String output = pResult.getOutputStream();
        String[] lines = output.split("\n");
        // StringBuffer proofBuffer = new StringBuffer();

        for (String line : lines) {
            if (line.equalsIgnoreCase("sat")) {
                state = QBFSolver.SAT;
                System.out.println("QBF/SAT");
                break;
            } else if (line.equalsIgnoreCase("unsat")) {
                state = QBFSolver.UNSAT;
                System.out.println("QBF/UNSAT");
                break;
            }

            // if (!line.equals("success") && !line.equals("sat") &&
            // !line.equals("unsat")) {
            // proofBuffer.append(line + "\n");
            // }
        }

        if (state == QBFSolver.NOT_RUN)
            state = QBFSolver.UNKNOWN;

        // it's really exit code 10 on success
        if (pResult.getExitCode() != 10) {
            System.out.println("EXIT CODE: " + pResult.getExitCode());
            System.out.println("ERROR:     " + pResult.getErrorStream());
            System.out.println("OUTPUT:    " + output);
        }
    }

    public int getState() {
        return state;
    }

    public static boolean isActive() {
        return isActive;
    }

    public static void setActive(boolean _isActive) {
        QBFSolver.isActive = _isActive;
    }

}
