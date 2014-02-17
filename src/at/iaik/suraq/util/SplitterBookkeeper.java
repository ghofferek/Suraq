/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class SplitterBookkeeper implements Runnable {

    private List<UncolorableLeafSplitter> splitters;

    private boolean killed = false;

    /**
     * 
     * Constructs a new <code>SplitterBookkeeper</code>.
     * 
     * @param splitters
     */
    public SplitterBookkeeper(
            Collection<? extends UncolorableLeafSplitter> splitters) {
        this.splitters = new ArrayList<UncolorableLeafSplitter>(splitters);
    }

    public SplitterBookkeeper(UncolorableLeafSplitter[] splitters) {
        this.splitters = new ArrayList<UncolorableLeafSplitter>(
                splitters.length);
        for (UncolorableLeafSplitter splitter : splitters)
            this.splitters.add(splitter);
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
        while (!killed) {
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
            synchronized (Util.class) {
                Util.printToSystemOutWithWallClockTimePrefix("    "
                        + "OVERALL: " + ": " + literalsFewer
                        + " literals saved so far in " + clausesStronger
                        + " clauses.");
                Util.printToSystemOutWithWallClockTimePrefix("    "
                        + "OVERALL " + ": " + "Done " + done + ". ("
                        + remaining + " remaining.)");
            }

            try {
                Thread.sleep(2 * 60 * 1000);
            } catch (InterruptedException exc) {
                System.out.println("Bookkeeper got interrupted!");
            }
        }
    }

}
