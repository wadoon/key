// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.runallproofs;

import java.io.IOException;
import java.util.Collection;
import java.util.Collections;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.StatisticsFile;

/**
 * This test case captures all Abstract Execution run-all-proof scenarios.
 *
 * The test case is controlled by the index file (see {@value #INDEX_FILE}).
 *
 * If the property "{@value #SKIP_AE_PROPERTY}" is set to true, then no Abstract
 * Execution run-all-proof tests will be run.
 *
 * @author Dominic Steinhoefel
 */
@RunWith(Parameterized.class)
public class RunAllProofsAbstractExecution extends RunAllProofsTest {
    public static final String SKIP_AE_PROPERTY = "key.runallproofs.skipAE";

    public static final String INDEX_FILE = "index/automaticAE.txt";

    private static ProofCollection proofCollection;

    public RunAllProofsAbstractExecution(RunAllProofsTestUnit unit) {
        super(unit);
    }

    @Parameters(name = "{0}")
    public static Collection<RunAllProofsTestUnit[]> data() throws IOException {
        if (Boolean.getBoolean(SKIP_AE_PROPERTY)) {
            return Collections.emptyList();
        }

        proofCollection = parseIndexFile(INDEX_FILE);
        return data(proofCollection);
    }

    @BeforeClass
    public static void setUpStatisticsFile() throws IOException {
        StatisticsFile statisticsFile = proofCollection.getSettings()
                .getStatisticsFile();
        statisticsFile.setUp();
    }

    @AfterClass
    public static void computeSumsAndAverages() throws IOException {
        StatisticsFile statisticsFile = proofCollection.getSettings()
                .getStatisticsFile();
        statisticsFile.computeSumsAndAverages();
    }

}