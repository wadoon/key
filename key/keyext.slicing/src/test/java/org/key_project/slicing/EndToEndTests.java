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
    void sliceAgatha() throws Exception {
        sliceProof("/agatha.proof", 145, 79);
    }

    @Test
    void sliceJavaExample() throws Exception {
        sliceProof("/removeDuplicates.zproof", 4960, 2626);
    }

    @Test
    void sliceCut() throws Exception {
        sliceProof("/cutExample.proof", 10, 7);
    }

    private void sliceProof(String filename, int expectedTotal, int expectedUseful) throws Exception {
        boolean oldValue = GeneralSettings.noPruningClosed;
        GeneralSettings.noPruningClosed = false;
        // load proof
        File proofFile = new File(testCaseDirectory, filename);
        Assertions.assertTrue(proofFile.exists());
        DependencyTracker tracker = new DependencyTracker();
        KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null, null, null, null, tracker, true);
        try {
            // get loaded proof
            Proof proof = environment.getLoadedProof();
            Assertions.assertNotNull(proof);
            // analyze proof
            var results = tracker.analyze();
            Assertions.assertEquals(expectedTotal, results.totalSteps);
            Assertions.assertEquals(expectedUseful, results.usefulStepsNr);
            // slice proof
            Proof slicedProof = tracker.sliceProof();

            // reload proof to verify the slicing was correct
            var tempFile = Files.createTempFile("", ".proof");
            slicedProof.saveToFile(tempFile.toFile());
            KeYEnvironment<?> loadedEnvironment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), tempFile.toFile(), null, null, null, null, null, null, true);
            try {
                slicedProof = loadedEnvironment.getLoadedProof();

                Assertions.assertEquals(expectedUseful + slicedProof.closedGoals().size(), slicedProof.countNodes());
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
