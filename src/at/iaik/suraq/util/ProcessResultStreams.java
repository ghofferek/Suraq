/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.io.BufferedReader;

/**
 * Stores the exit code and the output streams of an external process.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ProcessResultStreams {
    private final BufferedReader outputStream;
    private final BufferedReader errorStream;
    private final int exitCode;

    public ProcessResultStreams(BufferedReader outputStream,
            BufferedReader errorStream, int exitCode) {
        this.outputStream = outputStream;
        this.errorStream = errorStream;
        this.exitCode = exitCode;
    }

    /**
     * @return the <code>outputStream</code>
     */
    public BufferedReader getOutputStream() {
        return outputStream;
    }

    /**
     * @return the <code>errorStream</code>
     */
    public BufferedReader getErrorStream() {
        return errorStream;
    }

    /**
     * @return the <code>exitCode</code>
     */
    public int getExitCode() {
        return exitCode;
    }

}
