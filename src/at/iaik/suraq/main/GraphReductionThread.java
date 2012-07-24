package at.iaik.suraq.main;

import java.util.List;

import javax.xml.ws.Holder;

import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.util.Timer;

public class GraphReductionThread extends Thread
{
    private static int threads = 0;
    private int threadID = 0;
    private int from, to;
    private GraphReduction gr;
    private int circlesize;
    //private int circlecounter = 0;
    List<List<PropositionalVariable>> circles = null;
    
    public GraphReductionThread(GraphReduction gr, int from, int to)
    {
        threads++;
        threadID = threads;
        this.gr = gr;
        this.from = from;
        this.to = to;
        circles = gr.getCircles();
        circlesize = circles.size();
    }
    
    private int i;
    
    public void run()
    {
        while(true)
        {
            System.out.println("* Thread #"+threadID+" Started. From " + from + " to " + to );
            Timer timer = new Timer();
            timer.reset();
            for(i=from; i<to; i++)
            {
                timer.end();
                System.out.println("Thread #"+threadID+" - Search Circles #" +i + 
                        "/" + to + " = " + getProgress() + "% - Timer: " + timer.toString()); 
                timer.reset();timer.start();
                //System.out.println("Search Circles #"+i+"/"+circlesize+" Circles: "+circlecounter); 
                for(int j=i+1; j<circlesize; j++)
                {
                    gr.getSubFormula(circles.get(i), circles.get(j));
                }
            }
            System.out.println("* Tread #"+threadID+" ended the job! Searching for new one...");
            //if(!getWork()) // this method is synchronized
            {
                break;
            }
            //System.out.println("* Tread #"+threadID+" found a new job!");
        }
        System.out.println("* Tread #"+threadID+" ended the job! Didn't found a new job!");
    }
    
    public int getProgress()
    {
        return 100*(i-from)/(to-from);
    }
    
    private synchronized boolean getWork()
    {
        List<GraphReductionThread> threads = gr.getThreads();
        for(GraphReductionThread thread : threads)
        {
            Holder<Integer> _from = new Holder<Integer>();
            Holder<Integer> _to = new Holder<Integer>();
            if(thread.isAlive() && thread != this)
            {
                if(thread.takeWork(_from, _to))
                {
                    this.from = _from.value;
                    this.to = _to.value;
                    return true;
                }
            }
        }
        return false;
    }
    
    public synchronized boolean takeWork(Holder<Integer> _from, Holder<Integer> _to)
    {
        int progress = getProgress();
        System.out.println("Progress was "+progress);
        if(progress < 95 && (to - i) > 15) // min. 15 jobs and less than 95%
        {
            _to.value = to;
            to = to - (to - i - 2)/2;
            _from.value = to;
            return true;
        }
        return false;
    }
}
