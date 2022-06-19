package org.key_project.slicing;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.Pair;
import org.junit.Ignore;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;

class Evaluation {
    private static final Logger LOGGER = LoggerFactory.getLogger(Evaluation.class);

    public static final File testCaseDirectory = new File("/home/arne/Documents/KIT/BA/Evaluation/");

    // commented out file = doesn't load
    // TODO: re-check with disableOSSRestriction...
    private static final String[] FILES = new String[]{
            "01_Contraposition.key",
            "02_Liarsville.key",
            "03_AuntAgatha.key",
            "04_TransitivityOfSubset.key",
            "05_SumAndMax.zproof",
            "06_BinarySearch.zproof",
            "07_EnhancedFor.zproof",
            "08_RemoveDuplicates1.zproof",
            "08_RemoveDuplicates2.zproof",
            "08_RemoveDuplicates3.zproof",
            "09_SITA1.zproof",
            "09_SITA2.zproof",
            "09_SITA3.zproof",
            "10_SimpleArrayReversal.zproof",
            "11_PermutedSum_manual.zproof",
            "12_Quicksort_scripted.zproof",
            //"IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__VerifiedIdentityHashMap()).JML normal_behavior operation contract.0.proof.gz",
            "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__capacity(int)).JML normal_behavior operation contract.0.proof.gz",
            "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__capacity(int)).JML normal_behavior operation contract.1.proof.gz",
            "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__capacity(int)).JML normal_behavior operation contract.2.proof.gz",
            //"VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__clear()).JML normal_behavior operation contract.0.proof.gz",
            //"VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__containsKey(java.lang.Object)).JML normal_behavior operation contract.0.proof.gz",
            //"VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__containsMapping(java.lang.Object,java.lang.Object)).JML normal_behavior operation contract.0.proof.gz",
            //"VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__containsValue(java.lang.Object)).JML normal_behavior operation contract.0.proof.gz",
            //"VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__get(java.lang.Object)).JML normal_behavior operation contract.0.proof.gz",
            //"VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__get(java.lang.Object)).JML normal_behavior operation contract.1.proof.gz",
            "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__init(int)).JML normal_behavior operation contract.0.proof.gz",
            "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__isEmpty()).JML normal_behavior operation contract.0.proof.gz",
            "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__maskNull(java.lang.Object)).JML normal_behavior operation contract.0.proof.gz",
            "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__nextKeyIndex(int,int)).JML normal_behavior operation contract.0.proof.gz",
            //"VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__put(java.lang.Object,java.lang.Object)).JML exceptional_behavior operation contract.0.proof.gz",
            //"VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__put(java.lang.Object,java.lang.Object)).JML normal_behavior operation contract.0.proof.gz",
            //"VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__put(java.lang.Object,java.lang.Object)).JML normal_behavior operation contract.1.proof.gz",
            //"VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__resize(int)).JML exceptional_behavior operation contract.0.proof.gz",
            //"VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__resize(int)).JML normal_behavior operation contract.0.proof.gz",
            "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__resize(int)).JML normal_behavior operation contract.1.proof.gz",
            //"VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__resize(int)).JML normal_behavior operation contract.2.proof.gz",
            "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__size()).JML normal_behavior operation contract.0.proof.gz",
            "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__unmaskNull(java.lang.Object)).JML normal_behavior operation contract.0.proof.gz",
            //"DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__eInsertionSort((I,int,int,int,int,int,int,int)).JML normal_behavior operation contract.0.proof",
            "DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__loop_body((I,int,int,int,int,int)).JML normal_behavior operation contract.0.proof",
            "DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__move_great_left((I,int,int,int)).JML normal_behavior operation contract.0.proof",
            "DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__move_great_left_in_loop((I,int,int,int,int)).JML normal_behavior operation contract.0.proof",
            "DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__move_less_right((I,int,int,int)).JML normal_behavior operation contract.0.proof",
            "DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__prepare_indices((I,int,int)).JML normal_behavior operation contract.0.proof",
            "DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__sort((I)).JML normal_behavior operation contract.0.proof",
            "DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__sort((I,int,int,boolean)).JML normal_behavior operation contract.0.proof",
            "DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__split((I,int,int,int,int)).JML normal_behavior operation contract.0.proof",
            //"DualPivot_KeY_Proofs/overflow/ThreeWayQs/ThreeWayQs(ThreeWayQs__case_right((I,int,int,int,int)).JML normal_behavior operation contract.0.proof",
            //"DualPivot_KeY_Proofs/overflow/ThreeWayQs/ThreeWayQs(ThreeWayQs__sort((I)).JML normal_behavior operation contract.0.proof",
            //"DualPivot_KeY_Proofs/overflow/ThreeWayQs/ThreeWayQs(ThreeWayQs__sort((I,int,int)).JML normal_behavior operation contract.0.proof",
            //"DualPivot_KeY_Proofs/overflow/ThreeWayQs/ThreeWayQs(ThreeWayQs__split((I,int,int)).JML normal_behavior operation contract.0.proof",
            //"DualPivot_KeY_Proofs/permutation/DualPivotQuicksort_perm/calcE.proof",
            //"DualPivot_KeY_Proofs/permutation/DualPivotQuicksort_perm/split.proof",
            //"DualPivot_KeY_Proofs/permutation/DualPivotQuicksort_perm/split_I_int_int_int_int.proof",
            //"DualPivot_KeY_Proofs/permutation/SinglePivotPartition_perm/ThreeWayQs(ThreeWayQs__case_right((I,int,int,int,int)).JML normal_behavior operation contract.0.proof",
            "DualPivot_KeY_Proofs/permutation/SinglePivotPartition_perm/ThreeWayQs(ThreeWayQs__sort((I)).JML normal_behavior operation contract.0.proof",
            //"DualPivot_KeY_Proofs/permutation/SinglePivotPartition_perm/ThreeWayQs(ThreeWayQs__sort((I,int,int)).JML normal_behavior operation contract.0.proof",
            //"DualPivot_KeY_Proofs/permutation/SinglePivotPartition_perm/ThreeWayQs(ThreeWayQs__split((I,int,int)).JML normal_behavior operation contract.0.proof",
            "DualPivot_KeY_Proofs/permutation/SwapValues_perm/move_great_left.proof",
            "DualPivot_KeY_Proofs/permutation/SwapValues_perm/move_less_right.proof",
            //"DualPivot_KeY_Proofs/permutation/SwapValues_perm/swap_values.proof",
            "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/calcE.proof",
            "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/eInsertionSort_SavedAgain.proof",
            "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/loop_body.proof",
            "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/move_great_left.proof",
            "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/move_great_left_in_loop.proof",
            "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/move_less_right.proof",
            "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/prepare_indices.proof",
            "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/sort_I.proof",
            "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/sort_I_int_int.proof",
            "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/split.proof",
            //"DualPivot_KeY_Proofs/sort/SinglePivotPartition/caseRight.proof",
            "DualPivot_KeY_Proofs/sort/SinglePivotPartition/sort_I.proof",
            //"DualPivot_KeY_Proofs/sort/SinglePivotPartition/sort_I_int_int.proof",
            "DualPivot_KeY_Proofs/sort/SwapValues/move_great_left.proof",
            "DualPivot_KeY_Proofs/sort/SwapValues/move_less_right.proof",
            "DualPivot_KeY_Proofs/sort/SwapValues/swap_values.proof",
    };
    // Sizes:
    // 8, 14, 51, 63, 77, 127, 148, 189,
    // 320, 373, 417, 430, 441, 489, 493, 540, 611, 643, 658, 892,
    // 1133, 1140, 1245, 1471, 1582, 1814, 1858, 1928,
    // 2092, 2112, 2120, 2298, 2349, 2477, 2793, 3041, 3862, 4556, 4671, 4999, 5380, 6049,
    // 11272, 20623, 21615, 47352, 54572, 64968,
    // 110512, 120960, 162348

    @Test
    @Ignore("used during evaluation")
    void loadAll() {
        var working = 0;
        var total = 0;
        var failures = new ArrayList<>();
        var sizes = new ArrayList<Integer>();
        for (var filename : FILES) {
            LOGGER.info("Loading {}", filename);
            var loadedCorrectly = false;
            total++;
            try {
                var result = loadProof(filename);
                if (result != null) {
                    if (result.second.closed()
                            || (!result.first.getReplayResult().hasErrors()
                            && result.first.getReplayResult().getStatus().equals(IntermediateProofReplayer.SMT_NOT_RUN))) {
                        // NOTE: this assumes that such a status means it loaded successfully
                        // (i.e. setting up Z3 correctly would close the proof!)
                        loadedCorrectly = true;
                        sizes.add(result.second.countNodes());
                    }
                    result.first.dispose();
                }
            } catch (Exception e) {
                e.printStackTrace();
            }
            if (loadedCorrectly) {
                working++;
            } else {
                failures.add(filename);
            }
        }
        LOGGER.info("Loaded {}/{} proofs", working, total);
        sizes.sort(Comparator.naturalOrder());
        LOGGER.info("Sizes: {}", Arrays.toString(sizes.toArray()));
        if (working != total) {
            LOGGER.info("Failures:");
            for (var filename : failures) {
                LOGGER.info("{}", filename);
            }
        }
    }

    private Pair<KeYEnvironment<?>, Proof> loadProof(String filename) throws Exception {
        // load proof
        File proofFile = new File(testCaseDirectory, filename);
        Assertions.assertTrue(proofFile.exists());
        DependencyTracker tracker = new DependencyTracker();
        KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null, null, null, null, proof -> proof.addRuleAppListener(tracker), true);
        try {
            // get loaded proof
            Proof proof = environment.getLoadedProof();
            Assertions.assertNotNull(proof);

            return new Pair<>(environment, proof);
        } catch (Exception e) {
            environment.dispose();
            return null;
        }
    }

    private Proof sliceProof(String filename) throws Exception {
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
            // slice proof
            Proof slicedProof = tracker.sliceProof();

            // reload proof to verify the slicing was correct
            var tempFile = Files.createTempFile("", ".proof");
            slicedProof.saveToFile(tempFile.toFile());
            KeYEnvironment<?> loadedEnvironment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), tempFile.toFile(), null, null, null, null, null, null, true);
            try {
                slicedProof = loadedEnvironment.getLoadedProof();

                Assertions.assertTrue(slicedProof.closed());

                Files.delete(tempFile);

                return slicedProof;
            } finally {
                loadedEnvironment.dispose();
            }
        } finally {
            environment.dispose();
            GeneralSettings.noPruningClosed = oldValue;
        }
    }
}
