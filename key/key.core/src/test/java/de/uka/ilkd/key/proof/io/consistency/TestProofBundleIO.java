package de.uka.ilkd.key.proof.io.consistency;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.HelperClassForTests;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofBundleSaver;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import static org.junit.Assert.*;

/**
 * This class contains test cases for loading and saving proof bundles.
 *
 * @author Wolfram Pfeifer
 */
public class TestProofBundleIO {
    /** the resources path for this test */
    private static Path testDir;

    /** to reset the setting after the tests (usually should be false if not in GUI mode) */
    private static boolean ensureConsistency = false;

    /**
     * Set up the test path and store the current allowBundleSaving setting.
     */
    @BeforeClass
    public static void prepare() {
        testDir = Paths.get(HelperClassForTests.TESTCASE_DIRECTORY.getAbsolutePath(), "proofBundle");

        // remember settings to be able to reset after the test
        ensureConsistency = ProofIndependentSettings.DEFAULT_INSTANCE
                                                    .getGeneralSettings()
                                                    .isEnsureSourceConsistency();
    }

    /**
     * Reset settings to value before tests.
     */
    @AfterClass
    public static void cleanUp() {
        // reset the settings to value before test
        ProofIndependentSettings.DEFAULT_INSTANCE
                                .getGeneralSettings()
                                .setEnsureSourceConsistency(ensureConsistency);
    }

    /**
     * Tests loading a proof bundle and subsequent saving preserves the files in the bundle. As a
     * side effect, pruning of closed branches/proofs is tested in interplay with a merge rule.
     * <br><br>
     * This test performs the following steps:
     * <ol>
     * <li>loads the bundle, which opens the first proof in it (for method m)</li>
     * <li>prunes the proof to its root</li>
     * <li>saves the proof as a bundle again (this should update/replace the proof of m, but keep
     *      all other files in the repo intact)</li>
     * <li>unzips the bundle (to check if the expected files are present)</li>
     * <li>loads the single proof from the unzipped directory (tests that javaSrc directive is
     *      adapted correctly)</li>
     * </ol>
     * @throws Exception on errors (should not happen)
     */
    @Test
    public void testLoadSaveBundle() throws Exception {
        Path bundle = testDir.resolve("testbundle.zproof");

        // enable pruning of closed branches temporarily for the test
        boolean pruningDisabled = GeneralSettings.noPruningClosed;
        GeneralSettings.noPruningClosed = false;

        Proof proofForM = loadBundle(bundle);
        assertEquals("A[A::m(boolean)].JML operation contract.0", proofForM.name().toString());
        assertTrue(proofForM.closed());

        proofForM.pruneProof(proofForM.root());
        assertFalse(proofForM.closed());

        Path resavedBundle = testDir.resolve("testbundle_saved.zproof");
        ProofBundleSaver saver = new ProofBundleSaver(proofForM, resavedBundle.toFile());
        saver.save();

        Path unzip = resavedBundle.getParent().resolve("unzip");
        IOUtil.extractZip(resavedBundle, unzip);

        // test: classpath/bootclasspath empty (no such subdirectories exists)
        assertFalse(Files.exists(unzip.resolve("classpath")));
        assertFalse(Files.exists(unzip.resolve("bootclasspath")));

        // test: all files present in the original repo are present in the re-saved one
        assertTrue(Files.exists(unzip.resolve("src")));
        assertTrue(Files.exists(unzip.resolve("src").resolve("A.java")));
        assertTrue(Files.exists(unzip.resolve("src").resolve("Gcd.java")));
        assertTrue(Files.exists(unzip.resolve("A(A__f()).JML operation contract.0.proof")));
        assertTrue(Files.exists(unzip.resolve("A(A__g()).JML operation contract.0.proof")));

        Path singleProof = unzip.resolve("A(A__m(boolean)).JML operation contract.0.proof");
        assertTrue(Files.exists(singleProof));

        // test: the proof can be loaded again and was updated as expected by the pruning operation
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(singleProof.toFile());
        Proof reloadedProofForM = env.getLoadedProof();
        assertFalse(reloadedProofForM.closed());
        assertEquals(1, reloadedProofForM.countNodes());

        // clean up
        GeneralSettings.noPruningClosed = pruningDisabled;
        env.dispose();
        Files.delete(resavedBundle);
        IOUtil.delete(unzip.toFile());
    }

    /**
     * Tests loading a *.key file, closing the proof by auto mode, and saving a bundle from it.
     * Afterwards checks that the generated bundle is loadable again.
     * The *.key file includes bootclasspath and multiple classpath statements with *.java, *.class,
     * and *.zip files.
     * @throws Exception on errors (should not happen)
     */
    @Test
    public void testComplexBundleGeneration() throws Exception {
        /* size of file should be about 22 kb,
         * to be robust against small changes (or different compression),
         * we check only for 10 kb -> not empty */
        Path zip = testBundleGeneration("complexBundleGeneration", 10000);

        // test that bundle is loadable again and proof is closed
        Proof proof = loadBundle(zip);
        assertNotNull(proof);
        assertTrue(proof.closed());

        // clean up
        Files.delete(zip);
    }

    /**
     * Tests loading a *.key file, closing the proof by auto mode, and saving a bundle from it.
     * Afterwards checks that the generated bundle is loadable again and that it does not
     * contain unnecessary files (no classpath, no bootclasspath).
     * The *.key file only includes javaSource.
     * @throws Exception on errors (should not happen)
     */
    @Test
    public void testSimpleBundleGeneration() throws Exception {
        /* size of file should be about 2.5 kb,
         * to be robust against small changes (or different compression),
         * we check only for 1 kb -> not empty */
        Path zip = testBundleGeneration("simpleBundleGeneration", 1000);

        // test that bundle is loadable again and proof is closed
        Proof proof = loadBundle(zip);
        assertNotNull(proof);
        assertTrue(proof.closed());

        Path unzip = zip.getParent().resolve("unzip");
        IOUtil.extractZip(zip, unzip);

        // test: classpath/bootclasspath empty (no such subdirectories exists)
        assertFalse(Files.exists(unzip.resolve("classpath")));
        assertFalse(Files.exists(unzip.resolve("bootclasspath")));
        assertTrue(Files.exists(unzip.resolve("src")));

        // clean up
        Files.delete(zip);
        IOUtil.delete(unzip.toFile());
    }

    /**
     * Tests that the SimpleFileRepo is able to save a proof as bundle (without consistency).
     * @throws IOException on I/O errors
     */
    @Test
    public void testSimpleFileRepo() throws IOException {
        ProofIndependentSettings.DEFAULT_INSTANCE
                                .getGeneralSettings()
                                .setEnsureSourceConsistency(false);

        AbstractFileRepo simple = new SimpleFileRepo();
        Path base = testDir.resolve("simpleBundleGeneration");

        simple.setBaseDir(base);
        simple.setJavaPath(base.resolve("src").toString());

        Path src = base.resolve("src");
        InputStream is1 = simple.getInputStream(base.resolve("test.key"));
        InputStream is2 = simple.getInputStream(src.resolve("Client.java"));
        InputStream is3 = simple.getInputStream(src.resolve("Test.java"));

        Path zip = base.resolve("test.zproof");
        simple.saveProof(zip);

        assertNotNull(is1);
        assertNotNull(is2);
        assertNotNull(is3);
        assertTrue(Files.exists(zip));

        // clean up
        is1.close();
        is2.close();
        is3.close();
        Files.delete(zip);
    }

    /**
     * Loads a proof from a bundle.
     * @param p the path of the bundle
     * @return the loaded proof (currently, only a single proof is supported)
     * @throws ProblemLoaderException if loading fails
     */
    private Proof loadBundle(Path p) throws ProblemLoaderException {
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(p.toFile());
        assertNotNull(env);

        Proof proof = env.getLoadedProof();
        assertNotNull(proof);
        return proof;
    }

    /**
     * Helper method for tests. Does the following:
     * <ul>
     *   <li> loads a *.key file
     *   <li> tries to close the proof with auto mode
     *   <li> saves proof as a bundle.
     * </ul>
     * The saved bundle is deleted afterwards.
     * @param dirName the name of the directory with test resources (expects a file test.key here)
     * @param expectedSize the minimal size (in bytes) the generated bundle should have
     * @throws Exception on errors (should not happen)
     */
    private Path testBundleGeneration(String dirName, long expectedSize) throws Exception {
        // we test DiskFileRepo here!
        ProofIndependentSettings.DEFAULT_INSTANCE
                                .getGeneralSettings()
                                .setEnsureSourceConsistency(true);

        Path path = testDir.resolve(dirName).resolve("test.key");

        // load *.key file
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(path.toFile());
        assertNotNull(env);

        Proof proof = env.getLoadedProof();
        assertNotNull(proof);

        // start auto mode (proof is closable by auto mode)
        ProofControl control = env.getProofControl();
        control.startAndWaitForAutoMode(proof);
        assertTrue(proof.closed());

        // save (closed) proof as a bundle
        Path target = testDir.resolve(dirName).resolve("test.zproof");
        ProofBundleSaver saver = new ProofBundleSaver(proof, target.toFile());
        saver.save();

        // check if target file exists and has minimum size
        assertTrue(Files.exists(target));
        assertTrue(Files.size(target) >= expectedSize);

        return target;
    }
}
