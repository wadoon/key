package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.time.Duration;
import java.time.LocalDateTime;
import java.util.ArrayList;

import de.uka.ilkd.key.logic.Term;

public class CbiStats {

    private ArrayList<Long> unsolvedNanos;
    private ArrayList<Long> solvedNanos;
    private int calls;
    private int solved;
    private int callsWithEq;
    private int solvedWithEq;

    private CbiStats() {
        unsolvedNanos = new ArrayList<Long>();
        solvedNanos = new ArrayList<Long>();
        calls = 0;
        solved = 0;
        callsWithEq = 0;
        solvedWithEq = 0;
    }

    private static class InstanceHolder {
        private static final CbiStats INSTANCE = new CbiStats();
    }

    public static CbiStats getInstance() {
        return InstanceHolder.INSTANCE;
    }

    public void addStat(Term formula, LocalDateTime start, LocalDateTime end, Term result) {
        long nanos = Duration.between(start, end).toNanos();
        boolean eq = TermHelper.containsEqualityInScope(formula);
        boolean res = result != null;
        calls++;
        if(res) solved++;

        if(eq) {
            callsWithEq++;
            if(res) {
                solvedWithEq++;
                solvedNanos.add(nanos);
            }else {
                unsolvedNanos.add(nanos);
            }
        }else {
            if(res) System.out.println("CBI just solved without equality. This shouldn't even be possible.");
        }
        System.out.println("CBI:\teq: " + eq
                + ", \tnanos: " + nanos
                + ", \tsolved: " + (result != null)
                + ". \tStatistics: solvedAVG: " + solvedNanos.stream().mapToDouble(a -> a).average()
                + ", \tunsolvedAVG: " + unsolvedNanos.stream().mapToDouble(a -> a).average()
                + ", \tcalls: " + calls
                + ", \tcallsWithEq: " + callsWithEq
                + ", \tsucc: " + ((double)solved)/((double)calls)
                + ", \tsuccWithEq: " + ((double)solvedWithEq)/((double)callsWithEq));

    }
}
