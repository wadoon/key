package de.uka.ilkd.key.strategy.conflictbasedinst.statistics;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

public class CbiStatisticsPrinter {

    public static final String SEPARATOR = ";";

    public static void setUp(File statfile) {
        if(statfile.exists()) statfile.delete();
        try {
            statfile.createNewFile();
            String head = "NAME" + SEPARATOR
                    + "EM-CALLS" + SEPARATOR
                    + "EM-INST" + SEPARATOR
                    + "EM-MILLIS" + SEPARATOR
                    + "CBI-CALLS" + SEPARATOR
                    + "CBI-INST" + SEPARATOR
                    + "CBI-IND" + SEPARATOR
                    + "CBI-EQ" + SEPARATOR
                    + "CBI-MILLIS" + SEPARATOR
                    + "CBI-SUBMILLIS" + SEPARATOR
                    + "NORM-RULE" + SEPARATOR
                    + "NORM-ALG" + SEPARATOR
                    + "NORM-MILLIS" + SEPARATOR
                    + "RULEAPPS" + SEPARATOR
                    + "NODES" + SEPARATOR
                    + "BRANCHES" + SEPARATOR
                    + "MILLIS" + SEPARATOR
                    + "MEMORY(KB)" + SEPARATOR
                    + "CLOSED";
            FileWriter fw = new FileWriter(statfile);
            fw.write(head);
            fw.write(System.lineSeparator());
            fw.close();
        }catch (IOException e) {
            System.err.println("Could not create statistics file:" + e.getMessage());
        }
    }

    public static void append(File statfile, ProofStatistics ps) {
        if(CbiStatistics.disabled()) return;
        StringBuilder sb = new StringBuilder();
        append(sb, ps.getName());
        append(sb, ps.getEmatchings());
        append(sb, ps.getEmatchingInstances());
        append(sb, ps.getEmatchingMillis());
        append(sb, ps.getCbis());
        append(sb, ps.getCbiInstances());
        append(sb, ps.getCbiInducing());
        append(sb, ps.getCbiEquality());
        append(sb, ps.getCbiMillis());
        append(sb, ps.getCbiSubproofMillis());
        append(sb, ps.getNormByRule());
        append(sb, ps.getNormInBG());
        append(sb, ps.getNormalisationMillis());
        append(sb, ps.getRuleApps());
        append(sb, ps.getNodes());
        append(sb, ps.getBranches());
        append(sb, ps.getOverallMillis());
        append(sb, ps.getMemoryKiloBytes());
        sb.append(ps.isClosed());
        writeLine(sb.toString(), statfile);
    }

    private static void append(StringBuilder sb, String value) {
        sb.append(value);
        sb.append(SEPARATOR);
    }

    private static void append(StringBuilder sb, long value) {
        sb.append(value);
        sb.append(SEPARATOR);
    }

    public static void writeLine(String line, File statfile) {
        if(CbiStatistics.disabled()) return;
        assert statfile != null: "Cannot write statistics, statfile is null";
        try {
            FileWriter fw = new FileWriter(statfile, true);
            PrintWriter pw = new PrintWriter(fw, true);
            pw.println(line);
            pw.close();
            fw.close();
        }catch (IOException e) {
            System.err.println("Could not write to statistics file:" + e.getMessage());
        }
    }

}
