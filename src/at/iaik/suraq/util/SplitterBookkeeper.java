/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import at.iaik.suraq.main.SuraqOptions;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class SplitterBookkeeper implements Runnable {

    private List<UncolorableLeafSplitter> splitters;

    private List<Long> threadIds;

    private boolean killed = false;

    private final Timer wallclockTimer;

    private final int sleepTime = SuraqOptions.getInstance()
            .getSplitterBookkeeperSleepTime();

    /**
     * 
     * Constructs a new <code>SplitterBookkeeper</code>. <code>splitters</code>
     * and <code>threadIds</code> must be in the same order!!
     * 
     * @param splitters
     * @param threadIds
     */
    public SplitterBookkeeper(
            Collection<? extends UncolorableLeafSplitter> splitters,
            Collection<Long> threadIds, Timer timer) {
        assert (splitters.size() == threadIds.size());
        this.splitters = new ArrayList<UncolorableLeafSplitter>(splitters);
        this.threadIds = new ArrayList<Long>(threadIds);
        this.wallclockTimer = timer;
    }

    /**
     * 
     * Constructs a new <code>SplitterBookkeeper</code>. <code>splitters</code>
     * and <code>threadIds</code> must be in the same order!!
     * 
     * @param splitters
     * @param threadIds
     */
    public SplitterBookkeeper(UncolorableLeafSplitter[] splitters,
            Collection<Long> threadIds, Timer timer) {
        assert (splitters.length == threadIds.size());
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
                Thread.sleep(sleepTime * 1000);
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
                for (int count = 0; count < threadIds.size(); count++) {
                    long threadId = threadIds.get(count);
                    long increment = tmxb.getThreadCpuTime(threadId);
                    increment = increment >= 0 ? increment : splitters.get(
                            count).getTotalCpuTime();
                    assert (increment >= 0);
                    totalCpuTime += increment;
                }
                parallelizationRatio = totalCpuTime
                        / (wallclockTimer.getTotalTimeMillis() * 1000d * 1000d);
            }

            long totalWaitTime = 0;
            if (waitTime) {
                for (int count = 0; count < threadIds.size(); count++) {
                    long threadId = threadIds.get(count);
                    long increment = tmxb.getThreadInfo(threadId) == null ? splitters
                            .get(count).getTotalWaitTime() : tmxb
                            .getThreadInfo(threadId).getBlockedTime();
                    assert (increment >= 0);
                    totalWaitTime += increment;
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
                            + Util.veryLargeNumberFormatter
                                    .format(totalCpuTime));
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
