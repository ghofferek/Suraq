/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */

package at.iaik.suraq.util;

import java.text.DecimalFormat;

/**
 * Utility class for measuring execution times
 * 
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
public class Timer {

    /**
     * The start time.
     */
    private long startTime = 0;

    /**
     * The end time.
     */
    private long endTime = 0;

    /**
     * Time elapsed during previous runs.
     */
    private long elapsedTime = 0;

    /**
     * Starts the measure
     * 
     */
    public void start() {
        this.startTime = System.currentTimeMillis();
    }

    /**
     * Stops the timing
     * 
     */
    public void stop() {
        this.endTime = System.currentTimeMillis();
        this.elapsedTime += (this.endTime - this.startTime);
        this.startTime = 0;
        this.endTime = 0;
    }

    /**
     * Resets the timer.
     */
    public void reset() {
        startTime = 0;
        endTime = 0;
        elapsedTime = 0;
    }

    /**
     * Returns the total time.
     * 
     * @return the total time.
     */
    public long getTotalTimeMillis() {
        if (startTime != 0)
            return (System.currentTimeMillis() - this.startTime)
                    + this.elapsedTime;
        else
            return (this.endTime - this.startTime) + this.elapsedTime;
    }

    /**
     * Returns a pretty string of the total time in seconds.
     * 
     * @return the total as string representation, formatted in seconds.
     */
    @Override
    public String toString() {
        long totalTime = getTotalTimeMillis();
        if (totalTime > 1000) {
            DecimalFormat myFormatter = new DecimalFormat("###,###,###.###");
            String output = myFormatter.format(totalTime / 1000.0);
            return output + "s";
        } else {
            return totalTime + "ms";
        }
    }
}