/*
 * Copyright (C) 2012 IAIK, Graz University of Technology
 */

package at.iaik.suraq.util;

import at.iaik.suraq.util.BenchmarkTimer.GCInformation;

import java.util.Arrays;

public class Measurement {
    private static final String SEP = " ";

    // TODO hack! I don't like static counting
    private static final String DESC_HEAD = "description";
    private static int maxLen = DESC_HEAD.length();

    public final String description;
    public final long time;
    public final boolean success;
    public final long totalMemory;
    public final long freeMemory;
    public final long gcRuns;
    public final long gcTime;

    public Measurement(String description, long time, boolean success,
            long usedMemory, long freeMemory, GCInformation gc) {
        description = description.replaceAll("\\s", "_");

        this.description = description;
        this.time = time;
        this.success = success;
        this.totalMemory = usedMemory;
        this.freeMemory = freeMemory;
        this.gcRuns = gc.runs;
        this.gcTime = gc.time;

        if (description.length() > maxLen) {
            maxLen = description.length();
        }
    }

    public long ms() {
        return time / 1000000;
    }

    public String success() {
        if (success) {
            return "OK";
        } else {
            return "FAIL";
        }
    }

    public long used() {
        return totalMemory - freeMemory;
    }

    public static String header() {
        String formatString = "%-" + maxLen + "s" + SEP + "%9s" + SEP + "%6s"
                + SEP + "%10s" + SEP + "%10s" + SEP + "%10s" + SEP + "%6s"
                + SEP + "%7s";
        String header = String.format(formatString, DESC_HEAD, "time",
                "result", "total mem", "free mem", "used mem", "GC run",
                "GC time");
        String units = String.format(formatString, "", "ms", "", "byte",
                "byte", "byte", "", "ms");

        char[] arr = new char[header.length()];
        Arrays.fill(arr, '-');
        String line = new String(arr);

        return header + "\n" + units + "\n" + line;
    }

    @Override
    public String toString() {
        String formatString = "%-" + maxLen + "s" + SEP + "%9d" + SEP + "%6s"
                + SEP + "%10d" + SEP + "%10d" + SEP + "%10d" + SEP + "%6d"
                + SEP + "%7d";
        return String.format(formatString, description, ms(), success(),
                totalMemory, freeMemory, used(), gcRuns, gcTime);
    }
    
    public String toCSV()
    {
        String formatString = "%s;%d;%s;%d;%d;%d;%d;%d";
        return String.format(formatString, description, ms(), success(),
                totalMemory, freeMemory, used(), gcRuns, gcTime);
        
    }
}
