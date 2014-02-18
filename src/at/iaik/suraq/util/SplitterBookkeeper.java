/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class SplitterBookkeeper implements Runnable {

    private List<UncolorableLeafSplitter> splitters;

    private List<Long> threadIds;

    private boolean killed = false;

    private final Timer wallclockTimer;

    /**
     * 
     * Constructs a new <code>SplitterBookkeeper</code>.
     * 
     * @param splitters
     * @param threadIds
     */
    public SplitterBookkeeper(
            Collection<? extends UncolorableLeafSplitter> splitters,
            Collection<Long> threadIds, Timer timer) {
        this.splitters = new ArrayList<UncolorableLeafSplitter>(splitters);
        this.threadIds = new ArrayList<Long>(threadIds);
        this.wallclockTimer = timer;
    }

    /**
     * 
     * Constructs a new <code>SplitterBookkeeper</code>.
     * 
     * @param splitters
     * @param threadIds
     */
    public SplitterBookkeeper(UncolorableLeafSplitter[] splitters,
            Collection<Long> threadIds, Timer timer) {
        this.threadIds = new ArrayList<Long>(threadIds);
        this.splitters = new ArrayList<UncolorableLeafSplitter>(
                splitters.length);
        for (UncolorableLeafSplitter splitter : splitters)
            this.splitters.add(splitter);
        this.wallclockTimer = timer;
    }

    /**
     * Tell this bookkeeper to terminate.
     */
    public void kill() {
        killed = true;
    }

    /**
     * @see java.lang.Runnable#run()
     */
    @Override
    public void run() {
        do {
            try {
                // Thread.sleep(2 * 60 * 1000);
                Thread.sleep(1000);
            } catch (InterruptedException exc) {
                System.out.println("Bookkeeper got interrupted!");
            }
            int done = 0;
            int remaining = 0;
            int clausesStronger = 0;
            int literalsFewer = 0;
            for (UncolorableLeafSplitter splitter : splitters) {
                done += splitter.getDone();
                remaining += splitter.getRemaining();
                clausesStronger += splitter.getNumStrongerClauses();
                literalsFewer += splitter.getTotalLiteralsFewer();
            }

            ThreadMXBean tmxb = ManagementFactory.getThreadMXBean();
            boolean cpuTime = tmxb.isThreadCpuTimeSupported();
            boolean waitTime = tmxb.isThreadContentionMonitoringSupported();

            long totalCpuTime = 0;
            double parallelizationRatio = 0;
            if (cpuTime) {
                for (long threadId : threadIds)
                    totalCpuTime += tmxb.getThreadCpuTime(threadId);
                parallelizationRatio = totalCpuTime
                        / (wallclockTimer.getTotalTimeMillis() * 1000d * 1000d);
            }

            long totalWaitTime = 0;
            if (waitTime) {
                for (long threadId : threadIds) {
                    totalWaitTime += tmxb.getThreadInfo(threadId) == null ? 0
                            : tmxb.getThreadInfo(threadId).getBlockedTime();
                }
            }

            synchronized (Util.class) {
                Util.printToSystemOutWithWallClockTimePrefix("    "
                        + "OVERALL: " + ": " + literalsFewer
                        + " literals saved so far in " + clausesStronger
                        + " clauses.");
                Util.printToSystemOutWithWallClockTimePrefix("    "
                        + "OVERALL " + ": " + "Done " + done + ". ("
                        + remaining + " remaining.)");
                if (cpuTime) {
                    Util.printToSystemOutWithWallClockTimePrefix("    "
                            + "OVERALL: Total CPU time (ns): "
                            + Util.largeNumberFormatter.format(totalCpuTime));
                    Util.printToSystemOutWithWallClockTimePrefix("    "
                            + "OVERALL: Parallelization ratio: "
                            + parallelizationRatio);
                }
                if (waitTime) {
                    Util.printToSystemOutWithWallClockTimePrefix("    "
                            + "OVERALL: Wait time (ms): "
                            + Util.largeNumberFormatter.format(totalWaitTime));
                }
            }
        } while (!killed);
    }

}
