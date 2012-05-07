/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */

package at.iaik.suraq.util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

/**
 * Utility functions for running external executables.
 * 
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
public class ProcessUtil {
	
	/**
     * Runs an external process and gets the output and error stream.
     * 
     * @param executable
     *            path to the external executable
     * @return structure containing the process results.
     */
	public static ProcessResult runExternalProcess(String executable){
		int exitCode = -1;
		String outputStream=null;
		String errorStream=null;
		
		try {
            Process p = Runtime.getRuntime().exec(executable);
    
            BufferedReader input = new BufferedReader(new InputStreamReader(
                    p.getInputStream()));
            BufferedReader error = new BufferedReader(new InputStreamReader(
                    p.getErrorStream()));

            StringBuffer resultBuffer = new StringBuffer();
            
            String line;
            line = input.readLine();
            while (line != null && !line.trim().equals("--EOF--")) { 
                resultBuffer.append(line + "\n");
                line = input.readLine();
            }

            exitCode = p.exitValue();
            outputStream = resultBuffer.toString();

            resultBuffer = new StringBuffer();
            line = error.readLine();
            while (line != null && !line.trim().equals("--EOF--")) { 
            	resultBuffer.append(line + "\n");
                line = error.readLine();
            }
            errorStream = resultBuffer.toString();
     
        } catch (IOException e) {
            e.printStackTrace();
        }
		
		return new ProcessResult(outputStream,errorStream,exitCode);
	}
	
	
	/**
     * Runs an external process writes a string to stdin 
     * and gets the output and error stream.
     * 
     * @param executable
     *            path to the external executable
     * @param inputStr
     *            String to write to the process' stdin
     * @return structure containing the process results.
     */
	public static ProcessResult runExternalProcess(String executable, String inputStr){
		int exitCode = -1;
		String outputStream=null;
		String errorStream=null;
		
		try {
            Process p = Runtime.getRuntime().exec(executable);
    
            BufferedReader input = new BufferedReader(new InputStreamReader(
                    p.getInputStream()));
            BufferedReader error = new BufferedReader(new InputStreamReader(
                    p.getErrorStream()));
            
            BufferedWriter stdin = new BufferedWriter(new OutputStreamWriter(
                    p.getOutputStream()));
            
            stdin.write(inputStr);
            stdin.flush();
            stdin.close();

            StringBuffer resultBuffer = new StringBuffer();
            
            String line;
            line = input.readLine();
            while (line != null && !line.trim().equals("--EOF--")) { 
                resultBuffer.append(line + "\n");
                line = input.readLine();
            }

            exitCode = p.exitValue();
            outputStream = resultBuffer.toString();

            resultBuffer = new StringBuffer();
            line = error.readLine();
            while (line != null && !line.trim().equals("--EOF--")) { 
            	resultBuffer.append(line + "\n");
                line = error.readLine();
            }
            errorStream = resultBuffer.toString();
     
        } catch (IOException e) {
            e.printStackTrace();
        }
		
		return new ProcessResult(outputStream,errorStream,exitCode);
	}
}
