package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.merge.MergeRuleTests;
import de.uka.ilkd.key.util.HelperClassForTests;
import org.junit.Test;

import java.io.File;

/**
 * @author Alexander Weigl
 * @version 1 (11/16/20)
 */
public class EmbeddedCommandTests {
    private static final File TEST_RESOURCES_DIR_PREFIX = new File(HelperClassForTests.TESTCASE_DIRECTORY, "ecmd");

    @Test
    public void testSimple() {
        Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX, "ecmd.default.key");

    }

}
