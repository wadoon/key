package de.uka.ilkd.key.api;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.scripts.AutoCommand;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;
import org.junit.Assert;
import org.junit.Test;

import java.io.File;
import java.util.HashMap;

/**
 * @author Alexander Weigl
 * @version 1 (27.04.17)
 */
public class KeYApiTest {

    @Test public void testContrapositionAuto() throws ProblemLoaderException, ProofInputException, Exception {
        ProofManagementApi pm = KeYApi.loadFromKeyFile(
                new File("../key.ui/examples/standard_key/prop_log/contraposition.key").getAbsoluteFile());

        System.out.println(pm.getLoadedProof().getProof());
        for (Contract c : pm.getProofContracts()) {
            System.out.println(c);
        }

        ProofApi papi = pm.getLoadedProof();
        ScriptApi sapi = papi.getScriptApi();

        AutoCommand autoCmd = (AutoCommand) KeYApi.getScriptCommandApi().getScriptCommands("auto");

        Assert.assertNotNull(autoCmd);
        System.out.println(autoCmd);

        ProofScriptCommandCall autoCall = sapi.instantiateCommand(autoCmd, new HashMap<>());
        VariableAssignments va = new VariableAssignments();
        ScriptResults nodes = sapi.executeScriptCommand(autoCall, papi.getFirstOpenGoal(), va);

        System.out.println(pm.getLoadedProof().getProof());
    }
}
