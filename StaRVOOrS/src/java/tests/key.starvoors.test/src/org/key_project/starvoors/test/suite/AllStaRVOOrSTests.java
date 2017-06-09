/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.starvoors.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.starvoors.test.testcase.StaRVOOrSUtilTest;
import org.key_project.starvoors.test.testcase.StaRVOOrSWriteAndReadTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({ 
    StaRVOOrSUtilTest.class, //TODO: Adapt to the new version of the API
    StaRVOOrSWriteAndReadTest.class
})
public class AllStaRVOOrSTests {
}