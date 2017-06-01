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

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.Optional;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Before;
import org.key_project.util.java.IOUtil;

import de.tud.cs.se.ds.specstr.analyzer.Analyzer.AnalyzerResult;
import de.tud.cs.se.ds.specstr.util.Utilities;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public abstract class AbstractAnalyzerTest {
    private static final Logger logger = LogManager.getFormatterLogger();
    private static final String FUNCTIONAL_TESTS_RELATIVE_DIR = "/resources/testcase/analyzer/";
    private static final File TMP_DIR = new File(
            System.getProperty("java.io.tmpdir") + "/analyzerTests/");

    private String functionalTestsDir;

    @Before
    public void setUp() throws Exception {
        final File projectRoot = IOUtil
                .getProjectRoot(AbstractAnalyzerTest.class);
        functionalTestsDir = projectRoot + FUNCTIONAL_TESTS_RELATIVE_DIR;

        if (!TMP_DIR.exists()) {
            if (!TMP_DIR.mkdirs()) {
                Utilities.logErrorAndThrowRTE(logger,
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

        final Analyzer analyzer = new Analyzer(
                new File(functionalTestsDir, relPathToJavaFile),
                fullyQualifiedMethodDescriptor, Optional.of(outProofFile));
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
