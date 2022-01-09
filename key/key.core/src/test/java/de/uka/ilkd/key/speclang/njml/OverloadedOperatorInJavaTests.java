package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.HelperClassForTests;
import org.junit.Assert;
import org.junit.Test;

import java.io.File;

/**
 * @author Alexander Weigl
 * @version 1 (1/9/22)
 */
public class OverloadedOperatorInJavaTests {
    @Test public void loadGhostVariable() throws ProblemLoaderException {
        File keyfile = new File(HelperClassForTests.TESTCASE_DIRECTORY, "overloadedghost/Test.java");
        var env = KeYEnvironment.load(keyfile, null, null, null);
        Assert.assertNotNull(env);
        env.dispose();
    }
}
