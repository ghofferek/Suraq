/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */

package at.iaik.suraq.util;

/**
 * Utility data-structure containing the results of an external process.
 * 
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
public class ProcessResult {
	private final String outputStream;
	private final String errorStream;
	private final int exitCode;
	
	/**
     * Creates the Process-Result data-structure and sets it's
     * content.
     * 
     * @param out
     *            output stream of the process
     * @param err
     *            error stream of the process
     * @param exit
     *            exit-code of the process
     */
	public ProcessResult(String out, String err, int exit){
		this.outputStream=out;
		this.errorStream=err;
		this.exitCode=exit;
	}

	/**
     * Gets the content of the process output-stream
     * after process termination.
     * 
     * @return the output stream of the process.
     */
	public String getOutputStream() {
		return outputStream;
	}

	/**
     * Gets the content of the process error-stream
     * after process termination.
     * 
     * @return the error stream of the process.
     */
	public String getErrorStream() {
		return errorStream;
	}

	/**
     * Gets the process' exit-code.
     * 
     * @return exit-code of the process.
     */
	public int getExitCode() {
		return exitCode;
	}
}
