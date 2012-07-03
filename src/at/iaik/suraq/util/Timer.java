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
        if (startTime == 0)
            this.startTime = System.currentTimeMillis();
    }

    /**
     * Stops the timing
     * 
     */
    public void stop() {
        if (this.startTime == 0)
            return;
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
            return ((System.currentTimeMillis() - this.startTime) + this.elapsedTime);
        else
            return ((this.endTime - this.startTime) + this.elapsedTime);
    }

    /**
     * Returns a pretty string of the total time in seconds.
     * 
     * @return the total as string representation, formatted in seconds.
     */
    @Override
    public String toString() {
        long totalTime = getTotalTimeMillis();
        String result;
        if (totalTime < 1000) {
            DecimalFormat milliSecondsFormatter = new DecimalFormat("000");
            result = milliSecondsFormatter.format(totalTime) + "ms";
        } else if (totalTime >= 1000 && totalTime < 60000) {
            DecimalFormat secondsFormatter = new DecimalFormat("00.00");
            result = secondsFormatter.format(totalTime / 1000.0) + "s";
        } else if (totalTime >= 60000 && totalTime < 3600000) {
            DecimalFormat clockPartFormatter = new DecimalFormat("00");
            long minutes = (totalTime / 60000);
            long seconds = (totalTime % 60000);
            result = clockPartFormatter.format(minutes) + ":"
                    + clockPartFormatter.format(seconds) + "s";

        } else if (totalTime >= 3600000) {
            DecimalFormat clockPartFormatter = new DecimalFormat("00");
            DecimalFormat hourFormatter = new DecimalFormat("###00");
            long hours = (totalTime / 3600000);
            long minutes = (totalTime % 3600000);
            long seconds = (totalTime % 60000);

            result = hourFormatter.format(hours) + ":"
                    + clockPartFormatter.format(minutes) + ":"
                    + clockPartFormatter.format(seconds);
        } else {
            result = "ERROR IN TIMER!";
            assert (false);
        }
        return result;
    }
}