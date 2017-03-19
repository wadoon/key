package de.uka.ilkd.key.rule.join;

import java.io.File;

import org.junit.Test;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.ProofStarter;
import junit.framework.TestCase;

public class MergePointRuleTests extends TestCase {

    private static final String TEST_RESOURCES_DIR_PREFIX = "resources/testcase/mergePoint/";

    public MergePointRuleTests() {
        
    }

    @Test
    public void testITE() {
        final Proof proof = loadProof("Gcd.ITE.open.key");
        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }

    @Test
    public void testPredicateAbstraction() {
        final Proof proof = loadProof(
                "Gcd.predAbstr.open.key");
        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }


    @Test
    public void testNestedMergeBlockContract1() {
        final Proof proof = loadProof("Math_notNull.nested.key");
        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }

    @Test
    public void testNestedMergeBlockContract2() {
        final Proof proof = loadProof("Math_notNull.nested.2.key");
        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }
    
    @Test
    public void testTryInsideContract(){
        final Proof proof = loadProof("Math_divContract.key");
        //doesn't close at the first attempt
        startAutomaticStrategy(proof);
        assertFalse(proof.closed());
        //without doing anything special, the proof closed at the second attempt.
        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }


    private void startAutomaticStrategy(final Proof proof) {
        ProofStarter starter = new ProofStarter(false);
        starter.init(proof);
        starter.start();
    }

    static Proof loadProof(String proofFileName) {
        File proofFile = new File(TEST_RESOURCES_DIR_PREFIX + proofFileName);
        assertTrue(proofFile.exists());

        try {
            KeYEnvironment<?> environment = KeYEnvironment.load(
                    JavaProfile.getDefaultInstance(), proofFile, null, null,
                    null, true);
            Proof proof = environment.getLoadedProof();
            assertNotNull(proof);

            return proof;
        }
        catch (ProblemLoaderException e) {
            fail("Proof could not be loaded:\n" + e.getMessage());
            return null;
        }
    }

}
