package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.HelperClassForTests;
import org.junit.Test;
import org.key_project.util.collection.ImmutableList;

import java.io.File;
import java.io.IOException;
import java.net.URL;

import static org.junit.Assert.*;

/**
 * @author Alexander Weigl
 * @version 1 (11/3/20)
 */
public class TestLocalSymbols2 {
    private static final File TEST_RESOURCES_DIR_PREFIX =
            new File(HelperClassForTests.TESTCASE_DIRECTORY, "localSymbols/");

    // there was a bug.
    @Test
    public void testDoubleInstantiation() throws ScriptException, IOException, InterruptedException {
        KeYEnvironment<?> env = loadProof("doubleSkolem.key");
        assert env != null;
        Proof proof = env.getLoadedProof();
        String script = env.getProofScript().first;

        ProofScriptEngine pse = new ProofScriptEngine(script, new Location((URL) null, 1, 1));
        pse.execute(null, proof);

        ImmutableList<Goal> openGoals = proof.openGoals();
        assert openGoals.size() == 1;
        Goal goal = openGoals.head();
        String actual = goal.sequent().toString();
        assertEquals("[]==>[gt(i_0,Z(0(#))),lt(i_1,Z(0(#)))]", actual);
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof
     * is not null, and fails if the proof could not be loaded.
     *
     * @param proofFileName The file name of the proof file to load.
     * @return The loaded proof.
     */
    private KeYEnvironment<?> loadProof(String proofFileName) {
        File proofFile = new File(TEST_RESOURCES_DIR_PREFIX, proofFileName);
        assertTrue("Proof file does not exist" + proofFile, proofFile.exists());

        try {
            return KeYEnvironment.load(
                    JavaProfile.getDefaultInstance(), proofFile, null, null,
                    null, true);
        } catch (ProblemLoaderException e) {
            fail("Proof could not be loaded.");
            return null;
        }
    }
}
