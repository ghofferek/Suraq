/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */

package at.iaik.suraq.smtsolver;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;

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

		System.out.println("checking file: " + filename);

		String executionPath = basePath;
		if (mtEnabled)
			executionPath = executionPath.concat(mtBinPath);
		else
			executionPath = executionPath.concat(binPath);

		executionPath = executionPath.concat(binary);

		executionPath = executionPath.concat(" /smtc " + filename);

		try {
			Process p = Runtime.getRuntime().exec(executionPath);

			BufferedReader input = new BufferedReader(new InputStreamReader(
					p.getInputStream()));
			BufferedReader error = new BufferedReader(new InputStreamReader(
					p.getErrorStream()));

			String line;
			String lastline = null;
			
			StringBuffer outputString = new StringBuffer();

			System.out.println("OUTPUT from Z3:");
			while ((line = input.readLine()) != null) {
				if (!line.equals("success")){
					outputString.append(line + "\n");  
					System.out.println("   " + line);
					}
				lastline = line;
			}
			
			try {
	            File outputFile = new File("rsc/z3.out");

	            FileWriter fw = new FileWriter(outputFile);
	            fw.write(outputString.toString());
	            fw.close();
			}catch (IOException e) {
				e.printStackTrace();
	        }
			

			int exitCode = p.exitValue();

			System.out.println("EXIT CODE: " + exitCode);

			System.out.println("ERROR from Z3:");
			while ((line = error.readLine()) != null) {
				System.out.println("   " + line);
			}

			// last line seems to be Z3 outcome!
			if (lastline == null)
				state = UNKNOWN;
			else if (lastline.equals("sat"))
				state = SAT;
			else if (lastline.equals("unsat"))
				state = UNSAT;

		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
