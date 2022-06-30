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
 * Tests for the {@link DependencyTracker}, {@link DependencyAnalyzer}, {@link ProofSlicer}, ...
 *
 * @author Arne Keller
 */
class EndToEndTests {
    public static final File testCaseDirectory = FindResources.getTestCasesDirectory();

    // TODO: tests for: proof pruning, dot export, getNodeThatProduced

    @Test
    void sliceAgatha() throws Exception {
        sliceProof("/agatha.proof", 145, 79, 79);
    }

    @Test
    void sliceRemoveDuplicates() throws Exception {
        // simple Java proof
        sliceProof("/removeDuplicates.zproof", 4960, 2467, 2467);
    }

    @Test
    void sliceSitaRearrange() throws Exception {
        // this test case requires One Step Simplifactions to be restricted when slicing the proof
        Assertions.assertFalse(GeneralSettings.disableOSSRestriction);
        sliceProof("/sitaRearrange.zproof", 2722, 2162, 2162);
    }

    @Test
    void sliceCutExample() throws Exception {
        sliceProof("/cutExample.proof", 10, 7, 7);
    }

    @Test
    void sliceIfThenElseSplit() throws Exception {
        sliceProof("/ifThenElseSplit.proof", 12, 6, 6);
    }

    @Test
    void sliceSimpleSMT() throws Exception {
        sliceProof("/simpleSMT.proof", 1, 1, 0);
    }

    private Proof sliceProof(String filename, int expectedTotal, int expectedUseful, int expectedInSlice) throws Exception {
        boolean oldValue = GeneralSettings.noPruningClosed;
        GeneralSettings.noPruningClosed = false;
        // load proof
        File proofFile = new File(testCaseDirectory, filename);
        Assertions.assertTrue(proofFile.exists());
        DependencyTracker tracker = new DependencyTracker();
        KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null, null, null, null, proof -> proof.addRuleAppListener(tracker), true);
        try {
            // get loaded proof
            Proof proof = environment.getLoadedProof();
            Assertions.assertNotNull(proof);
            // analyze proof
            var results = tracker.analyze();
            Assertions.assertEquals(expectedTotal, results.totalSteps);
            Assertions.assertEquals(expectedUseful, results.usefulStepsNr);
            // slice proof
            var path = tracker.sliceProof();
            var env2 = KeYEnvironment.load(JavaProfile.getDefaultInstance(), path.toFile(), null, null, null, null, null, null, true);
            try {
                Proof slicedProof = env2.getLoadedProof();

                // reload proof to verify the slicing was correct
                var tempFile = Files.createTempFile("", ".proof");
                slicedProof.saveToFile(tempFile.toFile());
                KeYEnvironment<?> loadedEnvironment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), tempFile.toFile(), null, null, null, null, null, null, true);
                try {
                    slicedProof = loadedEnvironment.getLoadedProof();

                    Assertions.assertEquals(expectedInSlice + slicedProof.closedGoals().size(), slicedProof.countNodes());
                    Assertions.assertTrue(slicedProof.closed());

                    Files.delete(tempFile);

                    return slicedProof;
                } finally {
                    loadedEnvironment.dispose();
                }
            } finally {
                env2.dispose();
            }
        } finally {
            environment.dispose();
            GeneralSettings.noPruningClosed = oldValue;
        }
    }
}
