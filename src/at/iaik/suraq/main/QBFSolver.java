package at.iaik.suraq.main;

import at.iaik.suraq.util.ProcessResult;
import at.iaik.suraq.util.ProcessUtil;

public class QBFSolver {
	private static boolean isActive = false;
	
    public static final int NOT_RUN = 0;
    public static final int UNSAT = 1;
    public static final int SAT = 2;
    public static final int UNKNOWN = -1;
    
    private String qbfPath = "./lib/tools/depqbf/depqbf";
    private int state;
    
    public QBFSolver()
    {
        state = QBFSolver.NOT_RUN;
    }
    
    public void solve(String smtStr) {
        String executionPath = qbfPath;

        
        //if (System.getProperty("os.name").toLowerCase().contains("windows"))
        //    executionPath = executionPath.concat(" /smt2 /in");
        //else
        //    executionPath = executionPath.concat(" -smt2 -in");

        System.out.println("starting external process...");
        ProcessResult pResult = ProcessUtil.runExternalProcess(executionPath, smtStr);
        System.out.println("i'm back...");

        String output = pResult.getOutputStream();
        String[] lines = output.split("\n");
        //StringBuffer proofBuffer = new StringBuffer();

        for (String line : lines)
        {
            if (line.equalsIgnoreCase("sat"))
            {
                state = QBFSolver.SAT;
                System.out.println("QBF/SAT");
                break;
            }
            else if (line.equalsIgnoreCase("unsat"))
            {
                state = QBFSolver.UNSAT;
                System.out.println("QBF/UNSAT");
                break;
            }
            
            
           // if (!line.equals("success") && !line.equals("sat") && !line.equals("unsat")) {
           //     proofBuffer.append(line + "\n");
           // }
        }

        if (state == QBFSolver.NOT_RUN)
            state = QBFSolver.UNKNOWN;

       
        // it's really exit code 10 on success
        if (pResult.getExitCode() != 10)
        {
            System.out.println("EXIT CODE: " + pResult.getExitCode());
            System.out.println("ERROR:     " + pResult.getErrorStream());
            System.out.println("OUTPUT:    " + output);
        }
    }
    
    public int getState()
    {
        return state;
    }

	public static boolean isActive() {
		return isActive;
	}

	public static void setActive(boolean _isActive) {
		QBFSolver.isActive = _isActive;
	}
    
}
