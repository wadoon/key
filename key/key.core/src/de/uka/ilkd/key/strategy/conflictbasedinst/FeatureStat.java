package de.uka.ilkd.key.strategy.conflictbasedinst;

import de.uka.ilkd.key.logic.Term;

public class FeatureStat {

    private InstMethod method;
    private boolean eq;
    private boolean success;
    private NanoStopWatch featureSW;
    private NanoStopWatch subSW;
    private NanoStopWatch normSW;

    public FeatureStat(Term formula, InstMethod meth) {
        this.method = meth;
        this.eq = TermHelper.containsEqualityInScope(formula);
        this.success = false;
        featureSW = new NanoStopWatch();
        subSW = new NanoStopWatch();
        normSW = new NanoStopWatch();
    }

    public void start() {
        featureSW.start();
    }

    public void finish(boolean success) {
        this.success = success;
        featureSW.stop();
    }

    public void pause() {
        subSW.start();
    }

    public void resume() {
        subSW.stop();
    }

    public void startNormalization() {
        normSW.start();
    }

    public void finishNormalization() {
        normSW.stop();
    }

    public InstMethod getMethod() {
        return method;
    }

    public long getDuration() {
        return featureSW.getNanos();
    }

    public boolean isEq() {
        return eq;
    }

    public boolean isFound() {
        return success;
    }

    public long getSubduration() {
        return subSW.getNanos();
    }

    public long getNormalization() {
        return normSW.getNanos();
    }

    private class NanoStopWatch {

        private long tmp;
        private boolean counting;
        private long value;

        public NanoStopWatch() {
            tmp = 0;
            counting = false;
            value = 0;
        }

        public void start() {
            if(counting) throw new RuntimeException("Already counting.");
            counting = true;
            tmp = System.nanoTime();
        }

        public void stop() {
            if(!counting) throw new RuntimeException("Not counting.");
            value = System.nanoTime() - tmp;
            counting = false;
        }

        public long getNanos() {
            return value;
        }
    }


}
