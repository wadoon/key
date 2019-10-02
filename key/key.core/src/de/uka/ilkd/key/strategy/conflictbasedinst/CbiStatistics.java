package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.Term;

public class CbiStatistics {

    private static class InstanceHolder {
        private static final CbiStatistics INSTANCE = new CbiStatistics();
    }

    private static CbiStatistics instance() {
        return InstanceHolder.INSTANCE;
    }

    private static boolean enabled = false;

    public static void enable() {
        enabled = true;
    }

    public static void startProof(File keyFile) {
        String name = keyFile.getAbsolutePath();
        final int slashIndex = name.lastIndexOf("examples/");
        name = slashIndex >= 0 ? name.substring(slashIndex) : name;
        instance().startProof(name);
    }

    private CbiStatistics() {
        proofStatistics = new LinkedList<ProofStat>();
    }

    private ProofStat currentProofStat;
    private FeatureStat currentFeatureStat;
    private List<ProofStat> proofStatistics;

    private void startProof(String name) {
        if(!enabled) return;
        currentProofStat = new ProofStat(name);
        proofStatistics.add(currentProofStat);
    }

    public static void startFeature(Term formula, InstMethod meth) {
        if(!enabled) return;
        instance().currentFeatureStat = new FeatureStat(formula, meth);
        instance().currentFeatureStat.start();
    }

    public static void pauseFeatureStopwatch() {
        if(!enabled) return;
        instance().currentFeatureStat.pause();
    }

    public static void resumeFeatureStopwatch() {
        if(!enabled) return;
        instance().currentFeatureStat.resume();
    }

    public static void finishFeature(boolean succ) {
        if(!enabled) return;
        instance().currentFeatureStat.finish(succ);
        instance().currentProofStat.addStat(instance().currentFeatureStat);
    }

    public void flush(File statFile) {
        if(!enabled) return;
        StringBuilder sb = new StringBuilder();
        ProofStat ps = currentProofStat;
        sb.append(ps.getName());
        sb.append("|");
        List<FeatureStat> instStats = ps.getStats();
        long instCBI = 0;
        long instHEUR = 0;
        boolean eq = false;
        for(FeatureStat stat: instStats) {
            if(stat.getMethod() == InstMethod.CBI) {
                instCBI++;
            }else {
                instHEUR++;
            }
            eq = eq || stat.isEq();
        }
        sb.append(instStats.size());
        sb.append("|");
        sb.append(instCBI);
        sb.append("|");
        sb.append(instHEUR);
        sb.append("|");
        sb.append(eq);
        writeLine(sb.toString(), statFile);
    }

    // TODO File writing components to other class

    public static void append(File statFile) {
        if(!enabled) return;
        instance().flush(statFile);
    }

    private static void writeLine(String s, File statFile) {
        if(!enabled) return;
        if(statFile == null) {
            System.out.println("Could not write, statfile is null");
            return;
        }
        try {
            FileWriter fw = new FileWriter(statFile, true);
            PrintWriter pw = new PrintWriter(fw,true);
            pw.println(s);
            pw.close();
            fw.close();
        }
        catch (IOException e) {
            System.out.println("Could not write line to statistics file: " + e.getMessage());
        }

    }

    public static void setUp(File statFile) {
        enabled = true;
        if(statFile.exists()) statFile.delete();
        try {
            statFile.createNewFile();
            writeLine("NAME|#INST|#CBI|#HEUR|EQ", statFile);
        }
        catch (IOException e) {
            System.out.println("Could not create statistics file:" + e.getMessage());
        }
    }

    public static void startNormalization() {
        if(!enabled) return;
        instance().currentFeatureStat.startNormalization();
    }

    public static void finishNormalization() {
        if(!enabled) return;
        instance().currentFeatureStat.finishNormalization();
    }
}
