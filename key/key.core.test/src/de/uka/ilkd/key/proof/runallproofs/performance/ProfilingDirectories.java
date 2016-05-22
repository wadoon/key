package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;
import java.util.Date;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsDirectories;

@SuppressWarnings("serial")
public class ProfilingDirectories extends RunAllProofsDirectories {

    public final File profilingDataDir;
    public final File ruleIndependentDataDir;
    public final File ruleDependentDataDir;
    public final File computeCostDataDir;
    public final File instantiateAppDataDir;

    public ProfilingDirectories(Date runStart) {
        super(runStart);
        profilingDataDir = new File(runDir, "profilingData");
        ruleIndependentDataDir = new File(profilingDataDir, "ruleIndependentData");
        ruleIndependentDataDir.mkdirs();
        ruleDependentDataDir = new File(profilingDataDir, "ruleDependentData");
        computeCostDataDir = new File(ruleDependentDataDir, "computeCost");
        computeCostDataDir.mkdirs();
        instantiateAppDataDir = new File(ruleDependentDataDir, "instantiateApp");
        instantiateAppDataDir.mkdirs();
    }

}
