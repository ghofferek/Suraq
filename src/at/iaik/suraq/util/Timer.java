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
    public void end() {
        this.endTime = System.currentTimeMillis();
    }

    /**
     * Resets the timer.
     */
    public void reset() {
        startTime = 0;
        endTime = 0;
    }

    /**
     * Returns the start time.
     * 
     * @return the start time.
     */
    public long getStartTime() {
        return this.startTime;
    }

    /**
     * Returns the end time.
     * 
     * @return the end time.
     */
    public long getEndTime() {
        return this.endTime;
    }

    /**
     * Returns the total time.
     * 
     * @return the total time.
     */
    public long getTotalTime() {
        return this.endTime - this.startTime;
    }

    /**
     * Returns a pretty string of the total time in seconds.
     * 
     * @return the total as string representation, formatted in seconds.
     */
    @Override
    public String toString() {
        long totalTime = getTotalTime();
        if (totalTime > 1000) {
            DecimalFormat myFormatter = new DecimalFormat("###,###,###.###");
            String output = myFormatter.format(totalTime / 1000.0);
            return output + "s";
        } else {
            return totalTime + "ms";
        }
    }
}