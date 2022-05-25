package org.key_project.slicing;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.settings.GeneralSettings;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.key_project.util.helper.FindResources;

import java.io.File;

class EndToEndTests {
    public static final File testCaseDirectory = FindResources.getTestCasesDirectory();

    @Test
    void SliceAgatha() throws Exception {
        boolean oldValue = GeneralSettings.noPruningClosed;
        GeneralSettings.noPruningClosed = false;
        // Load proof
        File proofFile = new File(testCaseDirectory, "/agatha.proof");
        Assertions.assertTrue(proofFile.exists());
        DependencyTracker tracker = new DependencyTracker();
        KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null, null, null, null, tracker, true);
        try {
            // Get loaded proof
            Proof proof = environment.getLoadedProof();
            Assertions.assertNotNull(proof);
            // Analyze proof
            var results = tracker.analyze();
            Assertions.assertEquals(145, results.totalSteps);
            Assertions.assertEquals(79, results.usefulStepsNr);
            // Slice proof
            Proof slicedProof = tracker.sliceProof();
            // 79 rule applications + 3 closed goals
            Assertions.assertEquals(79 + 3, slicedProof.countNodes());
            Assertions.assertTrue(slicedProof.closed());
        }
        finally {
            environment.dispose();
        }
        GeneralSettings.noPruningClosed = oldValue;
    }
}
