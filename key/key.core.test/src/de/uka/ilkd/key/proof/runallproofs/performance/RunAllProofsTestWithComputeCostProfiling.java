package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.List;

import org.antlr.runtime.TokenStream;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import de.uka.ilkd.key.proof.runallproofs.Function;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsFunctional;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionParser;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * Same as {@link RunAllProofsFunctional} but we alter
 * {@link JavaCardDLStrategy#computeCost(de.uka.ilkd.key.rule.RuleApp, de.uka.ilkd.key.logic.PosInOccurrence, de.uka.ilkd.key.proof.Goal)}
 * so that statistical data about that method can be recorded (time duration,
 * number of invocations and potentially other stuff).
 */
@RunWith(Parameterized.class)
public class RunAllProofsTestWithComputeCostProfiling extends RunAllProofsTest {

    private static File dataDir;
    
    public static final File PROFILING_DIR = new File(RunAllProofsTest.RUNALLPROOFS_DIR, "profilingData");

    /**
     * Note: It is correct that this method takes the data directory as
     * parameter. Runallproofs subprocesses might use a different value than
     * local variable {@link #dataDir}.
     */
    static File instantiateAppDataDir(File dataDir) {
        File instantiateAppDataDir = new File(dataDir, "instantiateApp");
        instantiateAppDataDir.mkdirs();
        return instantiateAppDataDir;
    }

    /**
     * Note: It is correct that this method takes the data directory as
     * parameter. Runallproofs subprocesses might use a different value than
     * local variable {@link #dataDir}.
     */
    static File computeCostDataDir(File dataDir) {
        File computeCostDataDir = new File(dataDir, "computeCost");
        computeCostDataDir.mkdirs();
        return computeCostDataDir;
    }

    /**
     * Note: This static initialisation block should only be executed once for
     * each {@link RunAllProofsTestWithComputeCostProfiling} run. his can easily
     * be broken since fork mode of runallproofs re-executes static
     * initialisation blocks in each created subprocess. Be aware of that in
     * case you intend to change or move this block.
     */
    static void initDataDir() {
        SimpleDateFormat format = new SimpleDateFormat("dd.MMM_yyyy____HH:mm:ss");
        Date resultdate = new Date(System.currentTimeMillis());
        String date = format.format(resultdate);
        dataDir = new File(RunAllProofsTest.KEY_CORE_TEST,
                "testresults" + File.separator + "runallproofs" + File.separator + "performanceStatistics-" + date);
        dataDir.mkdirs();
    }

    public RunAllProofsTestWithComputeCostProfiling(RunAllProofsTestUnit unit) {
        super(unit);
    }

    @Parameters(name = "{0}")
    public static List<RunAllProofsTestUnit[]> data() throws Exception {
        initDataDir();
        ProofCollection proofCollection = parseIndexFile("index/automaticJAVADL.txt",
                new Function<TokenStream, ProofCollectionParser>() {
                    @Override
                    public ProofCollectionParser apply(TokenStream t) {
                        return new DataRecordingParser(t, dataDir);
                    }
                });
        proofCollection.getSettings().getStatisticsFile().setUp();
        return data(proofCollection);
    }

    static File plotScript;

    @BeforeClass
    public static void initPlotScriptLocation() throws IOException {
        plotScript = new File(
                KeYResourceManager.getManager().getResourceFile(RunAllProofsTestWithComputeCostProfiling.class,
                        File.separator + "plotscripts" + File.separator + "plot2png.sh").getFile());
        if (!plotScript.exists()) {
            throw new RuntimeException("Error: Script for creating plots not found!");
        }
    }

    @AfterClass
    public static void createPlots() throws IOException {
        createPlots(computeCostDataDir(dataDir));
        createPlots(instantiateAppDataDir(dataDir));
    }

    public static void createPlots(File dataDir) throws IOException {
        for (File ruleData : dataDir.listFiles()) {

            String ruleName = ruleData.getAbsolutePath();
            // /.../rulename.data -> /.../rulename [remove file ending]
            ruleName = ruleName.substring(0, ruleName.length() - 5);

            // gnuplot -e "ruledatalocation=' /.../rulename'" plot2png.sh
            ProcessBuilder pb = new ProcessBuilder("gnuplot", "-e", "ruledatalocation='" + ruleName + "'",
                    plotScript.getAbsolutePath());
            pb.inheritIO();
            // System.err.println("Plotting: " + dataDir.getName() + " " +
            // ruleData.getName());
            pb.start();
        }
    }

}
