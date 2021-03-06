/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */

package at.iaik.suraq.util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

import at.iaik.suraq.main.SuraqOptions;

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
    public static ProcessResult runExternalProcess(String executable) {
        int exitCode = -1;
        String outputStream = null;
        String errorStream = null;

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

            try {
                exitCode = p.waitFor();
            } catch (InterruptedException exc) {
                throw new RuntimeException("InterruptedException...", exc);
            }
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

        return new ProcessResult(outputStream, errorStream, exitCode);
    }

    /**
     * Runs an external process and gets the output and error stream as real
     * streams, instead of strings.
     * 
     * @param executable
     *            path to the external executable
     * @return structure containing the process results.
     */
    public static ProcessResultStreams runExternalProcessWithStreamResult(
            String executable) {
        int exitCode = -1;
        ProcessResultStreams result = null;
        try {
            // Process p = Runtime.getRuntime().exec(executable);
            //
            // BufferedReader input = new BufferedReader(new InputStreamReader(
            // p.getInputStream()));

            ProcessBuilder pb = new ProcessBuilder(executable.split(" "));
            File resultFile = File.createTempFile("z3Result", ".smt2",
                    new File("./"));
            if (!SuraqOptions.getInstance().getKeepTemFiles())
                resultFile.deleteOnExit();
            System.out.println("z3 Result file: " + resultFile.toString());
            pb.redirectOutput(resultFile);
            Process p = pb.start();
            BufferedReader error = new BufferedReader(new InputStreamReader(
                    p.getErrorStream()));
            try {
                exitCode = p.waitFor();
            } catch (InterruptedException exc) {
                throw new RuntimeException("InterruptedException...", exc);
            }
            FileReader freader = new FileReader(resultFile);
            BufferedReader input = new BufferedReader(freader);
            result = new ProcessResultStreams(input, error, exitCode);
        } catch (IOException exc) {
            throw new RuntimeException("IOException...", exc);
        }

        return result;
    }

    /**
     * Runs an external process writes a string to stdin and gets the output and
     * error stream.
     * 
     * @param executable
     *            path to the external executable
     * @param inputStr
     *            String to write to the process' stdin
     * @return structure containing the process results.
     */
    public static ProcessResult runExternalProcess(String executable,
            String inputStr) {
        int exitCode = -1;
        String outputStream = null;
        String errorStream = null;

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

            try {
                exitCode = p.waitFor();
            } catch (InterruptedException exc) {
                throw new RuntimeException("InterruptedException...", exc);
            }
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

        return new ProcessResult(outputStream, errorStream, exitCode);
    }
}
