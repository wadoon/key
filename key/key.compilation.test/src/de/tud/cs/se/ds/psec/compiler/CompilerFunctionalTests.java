package de.tud.cs.se.ds.psec.compiler;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

import org.junit.Test;
import org.key_project.util.java.IOUtil;

import de.tud.cs.se.ds.psec.parser.exceptions.TranslationTacletInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import junit.framework.TestCase;

/**
 * Functional test cases for the compiler (i.e., Java code is compiled,
 * executed, and tested for correctness).
 *
 * @author Dominic Scheurer
 */
public class CompilerFunctionalTests extends TestCase {
    private static final String FUNCTIONAL_TESTS_RELATIVE_DIR = "/resources/testcase/functional/";
    private static final String TMP_OUT_DIR = "./testTmp/";

    private String functionalTestsDir;

    @Override
    protected void setUp() throws Exception {
        Files.createDirectories(Paths.get(TMP_OUT_DIR));

        File projectRoot = IOUtil.getProjectRoot(CompilerFunctionalTests.class);
        functionalTestsDir = projectRoot + FUNCTIONAL_TESTS_RELATIVE_DIR;
    }

    @Override
    protected void tearDown() throws Exception {
        Files.delete(Paths.get(TMP_OUT_DIR));
    }

    @Test
    public void testTest() throws TranslationTacletInputException,
            ProblemLoaderException, IOException {

        Compiler compiler = new Compiler(
                new File(functionalTestsDir, "SimpleArithmeticAndIf.java"),
                TMP_OUT_DIR, true, true, false);

        compiler.compile();
    }

}
