package org.key_project.slicing;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.settings.GeneralSettings;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.key_project.util.helper.FindResources;

import java.io.File;
import java.nio.file.Files;

/**
 * Tests of the {@link DependencyTracker}.
 *
 * @author Arne Keller
 */
class EndToEndTests {
    public static final File testCaseDirectory = FindResources.getTestCasesDirectory();

    @Test
    void SliceAgatha() throws Exception {
        boolean oldValue = GeneralSettings.noPruningClosed;
        GeneralSettings.noPruningClosed = false;
        // load proof
        File proofFile = new File(testCaseDirectory, "/agatha.proof");
        Assertions.assertTrue(proofFile.exists());
        DependencyTracker tracker = new DependencyTracker();
        KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null, null, null, null, tracker, true);
        try {
            // get loaded proof
            Proof proof = environment.getLoadedProof();
            Assertions.assertNotNull(proof);
            // analyze proof
            var results = tracker.analyze();
            Assertions.assertEquals(145, results.totalSteps);
            Assertions.assertEquals(79, results.usefulStepsNr);
            // slice proof
            Proof slicedProof = tracker.sliceProof();
            // 79 rule applications + 3 closed goals
            Assertions.assertEquals(79 + 3, slicedProof.countNodes());
            Assertions.assertTrue(slicedProof.closed());
        } finally {
            environment.dispose();
        }
        GeneralSettings.noPruningClosed = oldValue;
    }

    @Test
    void SliceRemoveDuplicates() throws Exception {
        boolean oldValue = GeneralSettings.noPruningClosed;
        GeneralSettings.noPruningClosed = false;
        // load proof
        File proofFile = new File(testCaseDirectory, "/removeDuplicates.zproof");
        Assertions.assertTrue(proofFile.exists());
        DependencyTracker tracker = new DependencyTracker();
        KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null, null, null, null, tracker, true);
        try {
            // get loaded proof
            Proof proof = environment.getLoadedProof();
            Assertions.assertNotNull(proof);
            // analyze proof
            var results = tracker.analyze();
            Assertions.assertEquals(4960, results.totalSteps);
            Assertions.assertEquals(2626, results.usefulStepsNr);
            // slice proof
            Proof slicedProof = tracker.sliceProof();

            // reload proof to verify the slicing was correct
            var tempFile = Files.createTempFile("", ".proof");
            slicedProof.saveToFile(tempFile.toFile());
            KeYEnvironment<?> loadedEnvironment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), tempFile.toFile(), null, null, null, null, null, tracker, true);
            try {
                slicedProof = loadedEnvironment.getLoadedProof();

                // 2626 rule applications + closed goals
                Assertions.assertEquals(2626 + slicedProof.closedGoals().size(), slicedProof.countNodes());
                Assertions.assertTrue(slicedProof.closed());

                Files.delete(tempFile);
            } finally {
                loadedEnvironment.dispose();
            }
        } finally {
            environment.dispose();
        }
        GeneralSettings.noPruningClosed = oldValue;
    }
}
