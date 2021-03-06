/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.main;

import java.util.List;

import javax.xml.ws.Holder;

import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.util.Timer;

/**
 * not used!!! This thread was intended to improve performance in GraphReduction
 * to find additional Circles.
 * 
 * @author chillebold
 * 
 */
public class GraphReductionThread extends Thread {
    private static int threads = 0;
    private int threadID = 0;
    private int from, to;
    private GraphReduction gr;
    private int circlesize;
    List<List<PropositionalVariable>> circles = null;

    public GraphReductionThread(GraphReduction gr, int from, int to) {
        threads++;
        threadID = threads;
        this.gr = gr;
        this.from = from;
        this.to = to;
        circles = gr.getCircles();
        circlesize = circles.size();
    }

    private int i;

    @Override
    public void run() {
        while (true) {
            System.out.println("* Thread #" + threadID + " Started. From "
                    + from + " to " + to);
            Timer timer = new Timer();
            timer.reset();
            for (i = from; i < to; i++) {
                timer.end();
                System.out.println("Thread #" + threadID
                        + " - Search Circles #" + i + "/" + to + " = "
                        + getProgress() + "% - Timer: " + timer.toString());
                timer.reset();
                timer.start();
                // System.out.println("Search Circles #"+i+"/"+circlesize+" Circles: "+circlecounter);
                for (int j = i + 1; j < circlesize; j++) {
                    gr.getSubFormula(circles.get(i), circles.get(j));
                }
            }
            System.out.println("* Tread #" + threadID
                    + " ended the job! Searching for new one...");
            if (!getWork()) {
                break; // stop working if no other thread gave us work
            }
            // System.out.println("* Tread #"+threadID+" found a new job!");
        }
        System.out.println("* Tread #" + threadID
                + " ended the job! Didn't found a new job!");
    }

    /**
     * Returns the progress of the current job in Percent
     * @return
     */
    public int getProgress() {
        return 100 * (i - from) / (to - from);
    }

    /**
     * asks other threads for work. We need to look for other jobs, because some
     * jobs finish much faster than others!
     * 
     * @return
     */
    private synchronized boolean getWork() {
        List<GraphReductionThread> threads = gr.getThreads();
        for (GraphReductionThread thread : threads) {
            Holder<Integer> _from = new Holder<Integer>();
            Holder<Integer> _to = new Holder<Integer>();
            if (thread.isAlive() && thread != this) {
                if (thread.takeWork(_from, _to)) {
                    this.from = _from.value;
                    this.to = _to.value;
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * gives work to another thread
     * 
     * @param _from
     * @param _to
     * @return
     */
    public synchronized boolean takeWork(Holder<Integer> _from,
            Holder<Integer> _to) {
        int progress = getProgress();
        System.out.println("Progress was " + progress);
        if (progress < 95 && (to - i) > 15) // min. 15 jobs and less than 95%
        {
            _to.value = to;
            to = to - (to - i - 2) / 2;
            _from.value = to;
            return true;
        }
        return false;
    }
}
