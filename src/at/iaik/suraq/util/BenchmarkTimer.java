/*
 * Copyright (C) 2012 IAIK, Graz University of Technology
 */

package at.iaik.suraq.util;

import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Vector;

public class BenchmarkTimer {

    public class GCInformation {
        public long runs = 0;
        public long time = 0;

        public GCInformation(long runs, long time) {
            this.runs = runs;
            this.time = time;
        }
    }

    private final Map<GarbageCollectorMXBean, GCInformation> gcBeans = new HashMap<GarbageCollectorMXBean, GCInformation>();

    private long start;
    private Vector<Measurement> measurements = new Vector<Measurement>();
    private final Runtime rt = Runtime.getRuntime();

    public BenchmarkTimer() {
        start = System.nanoTime();
        List<GarbageCollectorMXBean> list = ManagementFactory
                .getGarbageCollectorMXBeans();
        for (GarbageCollectorMXBean bean : list) {
            long runs = bean.getCollectionCount();
            long time = bean.getCollectionTime();
            runs = runs > 0 ? runs : 0;
            time = time > 0 ? time : 0;
            gcBeans.put(bean, new GCInformation(runs, time));
        }
    }

    public void start() {
        start = System.nanoTime();
    }

    public long stopReset(String description) {
        long duration = System.nanoTime() - start;
        measurements.add(new Measurement(description, duration, true, rt
                .totalMemory(), rt.freeMemory(), getGCInformation()));
        start = System.nanoTime();
        return duration;
    }

    public long abortReset(String description) {
        long duration = System.nanoTime() - start;
        measurements.add(new Measurement(description, duration, false, rt
                .totalMemory(), rt.freeMemory(), getGCInformation()));
        start = System.nanoTime();
        return duration;
    }

    public Vector<Measurement> getResults() {
        return measurements;
    }

    private GCInformation getGCInformation() {
        long runs = 0;
        long time = 0;
        List<GarbageCollectorMXBean> list = ManagementFactory
                .getGarbageCollectorMXBeans();
        for (GarbageCollectorMXBean bean : list) {
            if (gcBeans.containsKey(bean)) {
                GCInformation info = gcBeans.get(bean);
                long thisRuns = bean.getCollectionCount();
                if (thisRuns > 0) {
                    runs += thisRuns - info.runs;
                    info.runs = thisRuns;
                }

                long thisTime = bean.getCollectionTime();
                if (thisTime > 0) {
                    time += thisTime - info.time;
                    info.time = thisTime;
                }
            } else {
                gcBeans.put(bean, new GCInformation(bean.getCollectionCount(),
                        bean.getCollectionTime()));
            }
        }
        return new GCInformation(runs, time);
    }
  
    @Override
    public String toString() {
        String out ="";// "Debug                                     ms  success    total       free       used    GC#  GCtime\n";
        out +=  Measurement.header()+"\n";
        //out +=       "---------------------------------------------------------------------------------------------------\n";
        for(Measurement measurement : measurements)
        {
            out += measurement.toString()+"\n";
        }
        return out;
    }
}
