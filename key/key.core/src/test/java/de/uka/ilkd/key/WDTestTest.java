package de.uka.ilkd.key;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.KeYTypeUtil;
import org.junit.Assert;
import org.junit.Test;
import org.key_project.util.collection.ImmutableSet;

import java.io.File;
import java.util.Collection;
import java.util.HashMap;
import java.util.Set;

/**
 * @author Alexander Weigl
 * @version 1 (2/26/20)
 */
public class WDTestTest {
    //public Collection<Object[]>

    @Test
    public void test() throws ProblemLoaderException, ProofInputException {
        if (!ProofSettings.isChoiceSettingInitialised()) {
            KeYEnvironment<?> env = KeYEnvironment.load(new File("/home/weigl/work/key/key/key.ui/examples/standard_key/prop_log/contraposition.key"));
            env.dispose();
        }
        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
        HashMap<String, String> oldSettings = choiceSettings.getDefaultChoices();
        try {
            //oldSettings.forEach((a, b) -> System.out.format("%s = %s\n", a, b));

            HashMap<String, String> newSettings = new HashMap<>(oldSettings);
            newSettings.put("wdChecks", "wdChecks:on");
            choiceSettings.setDefaultChoices(newSettings);

            // Load source code
            KeYEnvironment<?> env = KeYEnvironment.load(new File("/home/weigl/work/key/key/key.ui/examples/heap/vstte10_01_SumAndMax/SumAndMax_sumAndMaxWD.key"));

            Set<KeYJavaType> kjts = env.getJavaInfo().getAllKeYJavaTypes();
            for (KeYJavaType type : kjts) {
                if (!KeYTypeUtil.isLibraryClass(type)) {
                    ImmutableSet<IObserverFunction> targets = env
                            .getSpecificationRepository().getContractTargets(type);
                    for (IObserverFunction target : targets) {
                        ImmutableSet<Contract> contracts = env
                                .getSpecificationRepository()
                                .getContracts(type, target);
                        for (Contract contract : contracts) {
                            if(contract.getName().contains(" WD.")) {
                                runAuto(env, contract);
                            }
                        }
                    }
                }
            }

            env.dispose();
        } finally {
            choiceSettings.setDefaultChoices(oldSettings);
        }
    }

    private void runAuto(KeYEnvironment<?> env, Contract contract) throws ProofInputException {
        Proof proof = env.createProof(contract.getProofObl(env.getServices()));
        env.getProofControl().startAndWaitForAutoMode(proof);
        Assert.assertTrue(proof.closed());
    }
}
