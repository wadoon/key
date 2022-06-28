package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.io.consistency.TrivialFileRepo;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.ProgressMonitor;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;
import org.key_project.util.reflection.ClassLoaderUtil;

import java.io.IOException;
import java.lang.reflect.Method;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Properties;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

/**
 * This class contains test cases for well-definedness.
 *
 * @author Wolfram Pfeifer
 */
public class TestWellDefinedness {
    /** the path for resources of this test */
    private static Path testDir;

    /** used to restore the original taclet options after the test */
    private static HashMap<String, String> choicesBackup;

    /**
     * Set up the test path and store the current taclet options.
     */
    @BeforeAll
    public static void prepare() {
        testDir = Paths.get(HelperClassForTests.TESTCASE_DIRECTORY.getAbsolutePath(),
            "welldefinedness");

        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
        // store the current taclet options (use defaults as fallback)
        choicesBackup = choiceSettings.getDefaultChoices();
        if (choicesBackup.isEmpty()) {
            choicesBackup = MiscTools.getDefaultTacletOptions();
        }
        // change current taclet options to default, but overwrite welldefinedness options
        choiceSettings.setDefaultChoices(MiscTools.getDefaultTacletOptions());
        //ProofSettings.DEFAULT_SETTINGS.saveSettings();
        Set<Choice> choices = Set.of(new Choice("on", "wdChecks"), new Choice("L", "wdOperator"));
        choiceSettings.updateWith(choices);
    }

    /**
     * Reset taclet options to value before tests.
     */
    @AfterAll
    public static void cleanUp() {
        // we need to restore the settings file, because it has been overwritten by the test case
        ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().setDefaultChoices(choicesBackup);
        ProofSettings.DEFAULT_SETTINGS.saveSettings();
    }

    /**
     * Loads the well-definedness proof obligation from the file with the given path and runs the
     * auto mode on it. The proof is expected to be closed afterwards.
     * @param path the path of the test file relative to the test directory
     * @throws Exception we do not catch anything, any thrown exception will make the test case fail
     */
    @ParameterizedTest
    @ValueSource(strings = {"vstte10_01_SumAndMax/SumAndMax_sumAndMaxWD.key",  // TODO: more paths
                            "vstte10_01_SumAndMax/SumAndMax_sumAndMaxWithWDLoop.key"})
    void wellDefinednessTest(String path) throws Exception {
        Path wdTestPath = testDir.resolve(path);

        // load an unfinished proof from the file (the .key file contains "chooseContract xy")
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(wdTestPath.toFile());
        Proof proof = env.getLoadedProof();
        assertNotNull(proof);

        // start auto mode (proof is closable by auto mode)
        ProofControl control = env.getProofControl();
        control.startAndWaitForAutoMode(proof);
        assertTrue(proof.closed());
    }

    /**
     * This is an alternative version of the test case. It is much more complicated than the above
     * one, but provides a more fine-grained control and access to the internal data structures.
     * In case the above test case is not sufficient, this one can be used. Otherwise, this one
     * can be deleted.
     * @param path the path of the test file relative to the test directory
     * @throws Exception we do not catch anything, any thrown exception will make the test case fail
     */
    @ParameterizedTest
    @ValueSource(strings = {"vstte10_01_SumAndMax/SumAndMax_sumAndMaxWD.key",
                            "vstte10_01_SumAndMax/SumAndMax_sumAndMaxWithWDLoop.key"})
    void wellDefinednessTestAlt(String path) throws Exception {
        Path wdTestPath = testDir.resolve(path);

        Profile profile = AbstractProfile.getDefaultProfile();
        FileRepo fileRepo = new TrivialFileRepo();
        ProgressMonitor monitor = ProgressMonitor.Empty.getInstance();

        KeYUserProblemFile keyFile = new KeYUserProblemFile(wdTestPath.getFileName().toString(),
            wdTestPath.toFile(), fileRepo, monitor, profile, false);

        ProblemInitializer pi = new ProblemInitializer(monitor, new Services(profile),
            new DefaultUserInterfaceControl());
        pi.setFileRepo(fileRepo);

        InitConfig initConfig = pi.prepare(keyFile);
        initConfig.setFileRepo(fileRepo);

        LoadedPOContainer poContainer = createProofObligationContainer(keyFile, initConfig);
        assertNotNull(poContainer);

        ProofAggregate proofList = pi.startProver(initConfig, poContainer.getProofOblInput());
        assertEquals(1, proofList.getProofs().length);
        Proof proof = proofList.getFirstProof();

        // run the auto mode and make sure that the proof is closed afterwards
        UserInterfaceControl uic = new DefaultUserInterfaceControl();
        uic.getProofControl().startAndWaitForAutoMode(proof);
        assertTrue(proof.closed());
    }

    /**
     * Creates a {@link LoadedPOContainer} if available which contains
     * the {@link ProofOblInput} for which a {@link Proof} should be instantiated.
     * @return The {@link LoadedPOContainer} or {@code null} if not available.
     * @throws IOException Occurred Exception.
     */
    private static LoadedPOContainer createProofObligationContainer(KeYFile keyFile,
                                                                    InitConfig initConfig) throws IOException {
        // Note: adapted/simplified copy from AbstractProblemLoader
        final String chooseContract;
        final String proofObligation;

        chooseContract = keyFile.chooseContract();
        proofObligation = keyFile.getProofObligation();

        // Instantiate proof obligation
        if (keyFile instanceof ProofOblInput && chooseContract == null && proofObligation == null) {
            return new LoadedPOContainer((ProofOblInput)keyFile);
        } else if (chooseContract != null && chooseContract.length() > 0) {
            int proofNum = 0;
            String baseContractName = null;
            int ind = -1;
            for (String tag : FunctionalOperationContractPO.TRANSACTION_TAGS.values()) {
                ind = chooseContract.indexOf("." + tag);
                if (ind > 0) {
                    break;
                }
                proofNum++;
            }
            if (ind == -1) {
                baseContractName = chooseContract;
                proofNum = 0;
            } else {
                baseContractName = chooseContract.substring(0, ind);
            }
            final Contract contract = initConfig.getServices()
                .getSpecificationRepository()
                .getContractByName(baseContractName);
            if (contract == null) {
                throw new RuntimeException("Contract not found: " + baseContractName);
            } else {
                return new LoadedPOContainer(contract.createProofObl(initConfig), proofNum);
            }
        } else if (proofObligation != null && proofObligation.length() > 0) {

            Properties properties = new Properties();
            String poClass = properties.getProperty(IPersistablePO.PROPERTY_CLASS);
            if (poClass == null || poClass.isEmpty()) {
                throw new IOException("Proof obligation class property \"" + IPersistablePO.PROPERTY_CLASS + "\" is not defined or empty.");
            }
            try {
                // Try to instantiate proof obligation by calling static method: public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties) throws IOException
                Class<?> poClassInstance = ClassLoaderUtil.getClassforName(poClass);
                Method
                    loadMethod = poClassInstance.getMethod("loadFrom", InitConfig.class, Properties.class);
                return (LoadedPOContainer)loadMethod.invoke(null, initConfig, properties);
            } catch (Exception e) {
                throw new IOException("Can't call static factory method \"loadFrom\" on class \"" + poClass + "\".", e);
            }
        } else {
            return null;
        }
    }
}
