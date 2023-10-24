// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.tud.cs.se.ds.specstr.analyzer;

import static org.hamcrest.Matchers.containsString;
import static org.hamcrest.Matchers.equalTo;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.Optional;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.hamcrest.number.IsCloseTo;
import org.junit.Before;
import org.junit.Rule;
import org.junit.rules.ErrorCollector;
import org.key_project.util.java.IOUtil;

import de.tud.cs.se.ds.specstr.analyzer.Analyzer.AnalyzerResult;
import de.tud.cs.se.ds.specstr.util.GeneralUtilities;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * TODO
 *
 * @author Dominic Steinhoefel
 */
public abstract class AbstractAnalyzerTest {
    private static final Logger logger = LogManager.getFormatterLogger();
    private static final String FUNCTIONAL_TESTS_RELATIVE_DIR = "/resources/testcase/analyzer/";
    private static final File TMP_DIR = new File(
            System.getProperty("java.io.tmpdir") + "/analyzerTests/");
    
    // We assume that in each test case, only one Java file is under test, and
    // therefore we have a stable environment
    private KeYEnvironment<DefaultUserInterfaceControl> keyEnv = null;
    
    @Rule
    public final ErrorCollector collector = new ErrorCollector();

    public void assertEquals(int expected, int actual) {
        collector.checkThat(actual, equalTo(expected));
    }

    public void assertEquals(String expected, String actual) {
        collector.checkThat(actual, equalTo(expected));
    }

    public void assertEquals(double expected, double actual, double error) {
        collector.checkThat(actual, new IsCloseTo(expected, error));
    }

    public void assertContains(String expected, String completeString) {
        collector.checkThat(completeString, containsString(expected));
    }

    private String functionalTestsDir;

    @Before
    public void setUp() throws Exception {
        final File projectRoot = IOUtil
                .getProjectRoot(AbstractAnalyzerTest.class);
        functionalTestsDir = projectRoot + FUNCTIONAL_TESTS_RELATIVE_DIR;

        if (!TMP_DIR.exists()) {
            if (!TMP_DIR.mkdirs()) {
                GeneralUtilities.logErrorAndThrowRTE(logger,
                        "Could not create temporary directory %s",
                        TMP_DIR.getAbsolutePath());
            }
        }
    }

    /**
     * TODO
     * 
     * @param relPathToJavaFile
     * @param fullyQualifiedMethodDescriptor
     * @return
     * @throws ProblemLoaderException
     */
    protected AnalyzerResult analyzeMethod(String relPathToJavaFile,
            String fullyQualifiedMethodDescriptor) {
        final File outProofFile = new File(TMP_DIR,
                fullyQualifiedMethodDescriptor + ".proof");
        final File outResultsFile = new File(TMP_DIR,
                fullyQualifiedMethodDescriptor + ".txt");

        logger.info("Output file for proof: %s",
                outProofFile.getAbsolutePath());
        
        final File file = new File(functionalTestsDir, relPathToJavaFile);

        if (keyEnv == null) {
            try {
                keyEnv = new SymbExInterface(file).keyEnvironment();
            }
            catch (ProblemLoaderException e) {
                logger.error("Problem: %s", e.getMessage());
            }
        }
        
        final Analyzer analyzer = new Analyzer(
                file,
                fullyQualifiedMethodDescriptor, Optional.of(outProofFile),
                keyEnv);
        final AnalyzerResult result = analyzer.analyze();

        try {
            Analyzer.printResults(result,
                    new PrintStream(new FileOutputStream(outResultsFile)));
        } catch (FileNotFoundException e) {
            logger.error("Couldn't write results to file %s",
                    outResultsFile.getAbsolutePath());
        }

        return result;
    }
}
