package de.uka.ilkd.key.proof.runallproofs.performance;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsDirectories;

import java.io.File;
import java.text.SimpleDateFormat;
import java.util.Date;

public final class ProfilingDirectories {
    public static File profilingDataDir;
    public static File ruleIndependentDataDir;
    public static File ruleDependentDataDir;
    public static File computeCostDataDir;
    public static File instantiateAppDataDir;
    private static File runDir;

    ProfilingDirectories() {
    }

    public static void init(Date runStart) {
        if (runDir != null) return;
        SimpleDateFormat format = new SimpleDateFormat("dd.MMM_yyyy____HH:mm:ss");
        String date = format.format(runStart);
        runDir = new File(RunAllProofsDirectories.RUNALLPROOFS_DIR, "run-" + date);
        profilingDataDir = new File(runDir, "profilingData");
        ruleIndependentDataDir = new File(profilingDataDir, "ruleIndependentData");
        ruleDependentDataDir = new File(profilingDataDir, "ruleDependentData");
        computeCostDataDir = new File(ruleDependentDataDir, "computeCost");
        instantiateAppDataDir = new File(ruleDependentDataDir, "instantiateApp");

        ruleIndependentDataDir.mkdirs();
        computeCostDataDir.mkdirs();
        instantiateAppDataDir.mkdirs();
    }
}
