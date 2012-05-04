/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */

package at.iaik.suraq.smtsolver;

/**
 * 
 * This class acts as a factory for SMT-solver instances. It is able to support
 * different types of SMT-solvers.
 * 
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
public abstract class SMTSolver {

	/**
	 * Known SMT solver types.
	 */
	public static final int z3_type = 0;

	/**
	 * Describe the current state of a SMT-solver instance.
	 */
	public static final int NOT_RUN = 0;
	public static final int UNSAT = 1;
	public static final int SAT = 2;
	public static final int UNKNOWN = -1;
	
	/**
	 * Holds the proof of a satisfiability check, if present.
	 */
	protected String proof = null;

	/**
	 * Current SMT-solver state. Initial state is NOT_RUN.
	 */
	protected int state = NOT_RUN;

	/**
	 * Creates and parametrizes the given SMT-solver type.
	 * 
	 * @param solverType
	 *            the type of the SMT-solver to create.
	 * 
	 * @param solverBasePath
	 *            the base path of the external SMT-solver executable.
	 * 
	 * @return SMTSolver a SMT-solver instance of the given type.
	 */
	public static SMTSolver create(int solverType, String solverBasePath) {

		SMTSolver solver = null;

		switch (solverType) {
		case z3_type:
			solver = new z3(solverBasePath);
			solver.enableMultiThreaded();
			break;
		default:
			throw (new RuntimeException("unknown smt-solver requested."));
		}

		return solver;
	}

	/**
	 * Enables multi-threaded SMT-solver versions.
	 */
	protected abstract void enableMultiThreaded();

	/**
	 * Runs the SMT-solver instance with the given filename as input-file.
	 * 
	 * @param filename
	 *            SMT-solver input-file.
	 * 
	 */
	public abstract void solve(String filename);

	/**
	 * Returns the current state if an SMT-solver instance.
	 * 
	 * @return int current state code.
	 */
	public int getState() {
		return state;
	}

	/**
	 * Returns the proof of a satisfiability check.
	 * 
	 * @return String proof.
	 */
	public String getProof() {
		return proof;
	}

	/**
	 * Simplifies a smt string
	 * 
	 * @return the simplified string
	 */
	public abstract String simplify(String smtStr);

	/**
	 * Runs the SMT-solver instance with the given string as input.
	 * 
	 * @param smtStr
	 *            SMT-solver input.
	 * 
	 */
	public abstract void solveStr(String smtStr);
}
