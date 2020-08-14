package de.uka.ilkd.key.proof.runallproofs.performance;

import de.uka.ilkd.key.proof.runallproofs.ProofCollections;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsFunctional;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofGroup;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.experimental.categories.Category;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.key_project.util.testcategories.Performance;

import java.io.File;
import java.io.IOException;
import java.util.List;

/**
 * Same as {@link RunAllProofsFunctional} but we alter
 * {@link JavaCardDLStrategy#computeCost(de.uka.ilkd.key.rule.RuleApp, de.uka.ilkd.key.logic.PosInOccurrence, de.uka.ilkd.key.proof.Goal)}
 * so that statistical data about that method can be recorded (time duration,
 * number of invocations and potentially other stuff).
 */
@RunWith(Parameterized.class)
@Category(Performance.class)
public class RunAllProofsTestWithComputeCostProfiling extends RunAllProofsTest {
    public RunAllProofsTestWithComputeCostProfiling(ProofGroup unit) {
        super(unit);
    }

    @Parameters(name = "{0}")
    public static List<ProofGroup[]> data() throws Exception {
        ProofCollection proofCollection = ProofCollections.getJavaDlProofCollection();
        proofCollection.getSettings().getStatisticsFile().setUp();
        ProfilingDirectories.init(proofCollection.getSettings().runStart);
        return data(proofCollection);
    }

    static File plotScript;

    @BeforeClass
    public static void initPlotScriptLocation() throws IOException {
        plotScript = new File("../scripts/tools/runAllProofs_createPerformancePlots/plot2png.sh");
        if (!plotScript.exists()) {
            throw new RuntimeException("Error: Script for plot creation not found!");
        }
    }

    @AfterClass
    public static void createPlots() throws IOException {
        createPlots(ProfilingDirectories.computeCostDataDir);
        createPlots(ProfilingDirectories.instantiateAppDataDir);
    }

    public static void createPlots(File dataDir) throws IOException {
        for (File ruleData : dataDir.listFiles()) {
            String ruleName = ruleData.getAbsolutePath();
            // /.../rulename.data -> /.../rulename [remove file ending]
            ruleName = ruleName.substring(0, ruleName.length() - 5);

            // gnuplot -e "ruledatalocation=' /.../rulename'" plot2png.sh
            System.out.println("Plotting data for rule: " + ruleData.getName().split(".data")[0]);
            ProcessBuilder pb = new ProcessBuilder("gnuplot", "-e", "ruledatalocation='" + ruleName + "'",
                    plotScript.getAbsolutePath());
            pb.inheritIO();
            try {
                pb.start().waitFor();
            } catch (InterruptedException e) {
                System.out.println("InterruptedException: " + e.getMessage());
            }
        }
    }

}
