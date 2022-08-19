package org.key_project.slicing;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.Pair;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.key_project.util.helper.FindResources;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;

/**
 * Tests for the {@link DependencyTracker}, {@link DependencyAnalyzer}, {@link ProofSlicer}, ...
 *
 * @author Arne Keller
 */
class EndToEndTests {
    public static final File testCaseDirectory = FindResources.getTestCasesDirectory();

    // TODO tests for: proof pruning, dot export, getNodeThatProduced, running both algorithms...

    @Test
    void sliceAgatha() throws Exception {
        sliceProof("/agatha.proof", 145, 79, 79, true, false);
    }

    @Test
    void sliceRemoveDuplicates() throws Exception {
        // simple Java proof
        sliceProof("/removeDuplicates.zproof", 4960, 2467, 2467, true, false);
    }

    @Test
    void sliceSitaRearrange() throws Exception {
        // this test case requires One Step Simplifactions to be restricted when slicing the proof
        Assertions.assertFalse(GeneralSettings.disableOSSRestriction);
        sliceProof("/sitaRearrange.zproof", 2722, 2162, 2162, true, false);
    }

    @Test
    void sliceCutExample() throws Exception {
        sliceProof("/cutExample.proof", 10, 7, 7, true, false);
    }

    @Test
    void sliceIfThenElseSplit() throws Exception {
        sliceProof("/ifThenElseSplit.proof", 12, 6, 6, true, false);
    }

    @Test
    void sliceSimpleSMT() throws Exception {
        sliceProof("/simpleSMT.proof", 1, 1, 0, true, false);
    }

    @Test
    void sliceDuplicatesAway() throws Exception {
        var iteration1 = sliceProofFullFilename(new File(testCaseDirectory, "/exampleDuplicate.proof"), 10, 9, 9, false, true);
        var iteration2 = sliceProofFullFilename(iteration1.second.toFile(), 9, 8, 8, false, true);
        var iteration3 = sliceProofFullFilename(iteration2.second.toFile(), 8, 7, 7, false, true);
        var iteration4 = sliceProofFullFilename(iteration3.second.toFile(), 7, 7, 7, false, true);
        Files.delete(iteration4.second);
        Files.delete(iteration3.second);
        Files.delete(iteration2.second);
        Files.delete(iteration1.second);
    }

    private Proof sliceProof(String filename, int expectedTotal, int expectedUseful, int expectedInSlice, boolean doDependencyAnalysis, boolean doDeduplicateRuleApps) throws Exception {
        var it = sliceProofFullFilename(new File(testCaseDirectory, filename), expectedTotal, expectedUseful, expectedInSlice, doDependencyAnalysis, doDeduplicateRuleApps);
        Files.delete(it.second);
        return it.first;
    }

    private Pair<Proof, Path> sliceProofFullFilename(File proofFile, int expectedTotal, int expectedUseful, int expectedInSlice, boolean doDependencyAnalysis, boolean doDeduplicateRuleApps) throws Exception {
        boolean oldValue = GeneralSettings.noPruningClosed;
        GeneralSettings.noPruningClosed = false;
        // load proof
        Assertions.assertTrue(proofFile.exists());
        DependencyTracker tracker = new DependencyTracker();
        KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null, null, null, null, proof -> proof.addRuleAppListener(tracker), true);
        try {
            // get loaded proof
            Proof proof = environment.getLoadedProof();
            Assertions.assertNotNull(proof);
            // analyze proof
            var results = tracker.analyze(doDependencyAnalysis, doDeduplicateRuleApps);
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

                    return new Pair<>(slicedProof, tempFile);
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
