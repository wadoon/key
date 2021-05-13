package keyext.extract_preconditions;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.KeYTypeUtil;
import de.uka.ilkd.key.util.MiscTools;
import org.key_project.util.collection.ImmutableSet;

import java.io.File;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

/**
 * Class to try out precondition extraction.
 * Based on the Main Class in org.key_project.Main
 *
 * @author steuber
 */
public class ExtractorTest {
    private static final int MAX_STEPS = 10000;

    public static void main(String[] args) {
        if (args.length <= 0) {
            System.err.println("No file provided");
            return;
        }
        String javaFileName = args[0];
        File location = new File(javaFileName);
        if (!location.exists()) {
            System.err.println("File not found: " + javaFileName);
            return;
        }
        List<File> classPaths = null; // Optionally: Additional specifications for API classes
        File bootClassPath = null; // Optionally: Different default specifications for Java API
        List<File> includes = null; // Optionally: Additional includes to consider
        KeYEnvironment<?> env = null;
        try {
            try {
                env = createKeyEnvironment(location, classPaths, bootClassPath, includes);
            } catch (ProblemLoaderException e) {
                System.err.println("Failed loading file in KeY:");
                e.printStackTrace();
                return;
            }
            UserInterfaceControl ui = env.getUi();

            List<Proof> unclosedProofs = generateProofs(env);
            for (Proof currentProof : unclosedProofs) {
                PreconditionExtractor preconditionExtractor =
                    new PreconditionExtractor(currentProof, ui);
                Term precondition = preconditionExtractor.extract();
                System.out.println(
                    "Found precondition for " + currentProof.name() + ":\n" +
                        precondition.toString());
                currentProof.dispose();
            }
        } finally {
            if (env != null) {
                env.dispose();
            }
        }
    }

    private static List<Proof> generateProofs(KeYEnvironment<?> env) {
        // TODO(steuber): We probably want to adjust this a little? Or make it configurable...
        List<Proof> unclosedProofs = new LinkedList<Proof>();
        // List all specifications of all types in the source location (not classPaths and bootClassPath)
        final List<Contract> proofContracts = new LinkedList<Contract>();
        Set<KeYJavaType> kjts = env.getJavaInfo().getAllKeYJavaTypes();
        for (KeYJavaType type : kjts) {
            if (!KeYTypeUtil.isLibraryClass(type)) {
                ImmutableSet<IObserverFunction> targets =
                    env.getSpecificationRepository().getContractTargets(type);
                for (IObserverFunction target : targets) {
                    ImmutableSet<Contract> contracts =
                        env.getSpecificationRepository().getContracts(type, target);
                    for (Contract contract : contracts) {
                        proofContracts.add(contract);
                    }
                }
            }
        }
        // Perform proofs
        for (Contract contract : proofContracts) {
            Proof proof = null;
            try {
                // Create proof
                proof =
                    env.createProof(contract.createProofObl(env.getInitConfig(), contract));
                // Set proof strategy options
                StrategyProperties sp =
                    proof.getSettings().getStrategySettings().getActiveStrategyProperties();
                sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY,
                    StrategyProperties.METHOD_CONTRACT);
                sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY,
                    StrategyProperties.DEP_ON);
                sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY,
                    StrategyProperties.QUERY_ON);
                sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
                    StrategyProperties.NON_LIN_ARITH_DEF_OPS);
                sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY,
                    StrategyProperties.STOPMODE_NONCLOSE);
                proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
                // Make sure that the new options are used
                int maxSteps = MAX_STEPS;
                ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxSteps);
                ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                    .setActiveStrategyProperties(sp);
                proof.getSettings().getStrategySettings().setMaxSteps(maxSteps);
                proof.setActiveStrategy(
                    proof.getServices().getProfile().getDefaultStrategyFactory()
                        .create(proof, sp));
                // Start auto mode
                env.getUi().getProofControl().startAndWaitForAutoMode(proof);
                // Show proof result
                boolean closed = proof.openGoals().isEmpty();
                if (!closed) {
                    unclosedProofs.add(proof);
                }
            } catch (ProofInputException e) {
                System.out.println("Exception at '" + contract.getDisplayName() + "' of " +
                    contract.getTarget() + ":");
                e.printStackTrace();
            } finally {
                if (proof != null && proof.openGoals().isEmpty()) {
                    proof
                        .dispose(); // Ensure always that all instances of Proof are disposed
                }
            }
        }
        return unclosedProofs;
    }

    private static KeYEnvironment<?> createKeyEnvironment(File location, List<File> classPaths,
                                                          File bootClassPath, List<File> includes)
        throws ProblemLoaderException {
        // Ensure that Taclets are parsed
        if (!ProofSettings.isChoiceSettingInitialised()) {
            KeYEnvironment<?>
                env = KeYEnvironment.load(location, classPaths, bootClassPath, includes);
            env.dispose();
        }
        // Set Taclet options
        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
        HashMap<String, String> oldSettings = choiceSettings.getDefaultChoices();
        HashMap<String, String> newSettings = new HashMap<String, String>(oldSettings);
        newSettings.putAll(MiscTools.getDefaultTacletOptions());
        choiceSettings.setDefaultChoices(newSettings);
        // Load source code
        KeYEnvironment<?> env = KeYEnvironment.load(location, classPaths, bootClassPath,
            includes); // env.getLoadedProof() returns performed proof if a *.proof file is loaded
        return env;
    }
}
