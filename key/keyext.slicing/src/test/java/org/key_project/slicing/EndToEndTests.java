package org.key_project.slicing;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.key_project.util.helper.FindResources;

import java.io.File;

public class EndToEndTests {
    public static final File testCaseDirectory = FindResources.getTestCasesDirectory();

    @Test
    public void SliceAgatha() throws Exception {
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
            Assertions.assertEquals(new AnalysisResults(145, 79), tracker.analyze());
            // Slice proof
            Proof slicedProof = tracker.sliceProof();
            // 79 rule applications + 3 closed goals
            Assertions.assertEquals(79 + 3, slicedProof.countNodes());
            Assertions.assertTrue(slicedProof.closed());
        }
        finally {
            environment.dispose();
        }
    }
}
