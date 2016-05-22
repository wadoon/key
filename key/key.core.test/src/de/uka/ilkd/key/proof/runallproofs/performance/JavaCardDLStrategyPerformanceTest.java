package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import org.junit.Test;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsDirectories;
import de.uka.ilkd.key.strategy.Strategy;

public class JavaCardDLStrategyPerformanceTest {

    private static Info applyStrategy(String s) throws ProblemLoaderException {
        return applyStrategy(KeYEnvironment.load(s).getLoadedProof());
    }

    public static Info applyStrategy(Proof proof) {
        ModifiedStrategy strategy = new ModifiedStrategy(proof);
        ApplyStrategyInfo applyStrategyInfo = applyStrategy(proof, strategy);
        return new Info(applyStrategyInfo, strategy.computeCostInvocations, strategy.computeCostTotalTimeNano, proof);
    }

    public static ApplyStrategyInfo applyStrategy(Proof proof, Strategy strategy) {
        proof.setActiveStrategy(strategy);
        ApplyStrategyInfo applyStrategyInfo = new ApplyStrategy(proof).start(proof, proof.openGoals().head());
        return applyStrategyInfo;
    }

    // Helper method.
    String getRepeatedPart(String begin, String repeatedBegin, String repeatedEnd, String end, int repetitions) {
        StringBuilder sb = new StringBuilder(begin);
        for (int i = 0; i < repetitions + 1; i++) {
            sb.append(repeatedBegin + i + repeatedEnd);
        }
        sb.append(end);
        return sb.toString();
    }

    String formula2(int i) {
        if (i == 0) {
            return "true";
        }
        StringBuilder sb = new StringBuilder();
        sb.append("("); // Opening brace.
        sb.append("a" + i + " > 1 -> ");
        sb.append("\\forall int i; (p" + i + "(\\if (i > 0) \\then (i) \\else (0))) -> ");
        sb.append("p" + i + "(a" + i + ")");
        sb.append(")"); // Closing brace.
        if (i > 1) {
            return "(" + sb.toString() + "->" + formula2(i - 1) + ")";
        } else {
            return sb.toString();
        }
    }

    String problem2(int i) {
        StringBuilder sb = new StringBuilder();
        sb.append(getRepeatedPart("\\functions {\n", "int a", ";\n", "}\n\n", i));
        sb.append(getRepeatedPart("\\predicates {\n", "p", "(int);\n", "}\n\n", i));
        sb.append("\\problem {\n");
        sb.append(formula2(i));
        sb.append("\n}\n");

        return sb.toString();
    }

    String formula1(int i) {
        if (i == 0) {
            return "true";
        }
        StringBuilder sb = new StringBuilder();
        sb.append("("); // Opening brace.
        sb.append("(\\forall int i; (p" + i + "(i))->p" + i + "(1))");
        sb.append(")"); // Closing brace.
        if (i > 1) {
            return "(" + sb.toString() + "&" + formula1(i - 1) + ")";
        } else {
            return sb.toString();
        }
    }

    String problem1(int i) {
        StringBuilder sb = new StringBuilder();
        sb.append(getRepeatedPart("\\predicates {\n", "p", "(int);\n", "}\n\n", i));
        sb.append("\\problem {\n");
        sb.append(formula1(i));
        sb.append("\n}\n");
        return sb.toString();
    }

    String p(int i) {
        StringBuilder sb = new StringBuilder();
        sb.append("("); // Opening brace.
        for (int j = 0; j <= i; j++) {
            sb.append(j > 0 ? "&" : "");
            sb.append("p" + j + "(" + i + ")");
        }
        sb.append(")"); // Closing brace.
        return sb.toString();
    }

    String formula(int i, int k) {
        StringBuilder sb = new StringBuilder();
        sb.append("("); // Opening brace.
        sb.append("(\\forall int i; (p" + i + "(i))) -> \n");
        sb.append("("); // Opening brace.
        sb.append("(" + p(i) + ")");
        if (k > 0) {
            sb.append(" & (" + formula(i + 1, k - 1) + ")");
        }
        sb.append(")"); // Closing brace.
        sb.append(")"); // Closing brace.
        return sb.toString();
    }

    String problem(int i) {
        StringBuilder sb = new StringBuilder();
        sb.append(getRepeatedPart("\\predicates {\n", "p", "(int);\n", "}\n\n", i));
        sb.append("\\problem {\n");
        sb.append(formula(0, i));
        sb.append("\n}\n");
        return sb.toString();
    }

    String col1 = "# problem.length()";
    String col2 = " computeCostInvocations";
    String col3 = " averageTimeForComputeCost (in nanoseconds)";

    @Test
    public void test() throws ProblemLoaderException, IOException {
        File plotDataDir = new File(RunAllProofsDirectories.KEY_CORE_TEST, "testresults" + File.separator + "plot");
        plotDataDir.mkdirs();
        try (FileWriter writer = new FileWriter(new File(plotDataDir, "data.csv"))) {
            printLine(writer, col1, col2, col3);
            printLine(writer, 0 + "", 0 + "", 0 + ""); // make sure plot starts
                                                       // at point of origin
            for (int i = 0; i < 30; i++) {
                System.out.println(i);
                String problem = problem(i);
                // String problem = problem1(i);
                // String problem = problem2(i);
                System.out.println(problem);
                Info info = applyStrategy(problem);
                System.out.println(info.times());
                if (i > 5)
                    printLine(writer, problem.length() + "", info.computeCostInvocations + "",
                            info.averageTimeForComputeCost + "");
            }
        }
        runScript(plotDataDir, "avgTime.sh");
        runScript(plotDataDir, "nrInvocations.sh");
    }

    private void printLine(FileWriter writer, String x, String y1, String y2) throws IOException {
        writer.write(String.format("%1$" + col1.length() + "s", x));
        writer.write(String.format("%1$" + col2.length() + "s", y1));
        writer.write(String.format("%1$" + col3.length() + "s", y2));
        writer.write("\n");
    }

    private void runScript(File plotDataDir, String scriptName) throws IOException {
        File script = new File(RunAllProofsDirectories.KEY_CORE_TEST,
                "resources" + File.separator + "plotscripts" + File.separator + scriptName);
        ProcessBuilder pb = new ProcessBuilder(script.getAbsolutePath());
        pb.directory(plotDataDir);
        pb.start();
    }
}
