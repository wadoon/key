// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.rule.abstractexecution;

import org.junit.Test;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.HelperClassForTests;
import junit.framework.TestCase;

/**
 * @author Dominic Steinhoefel
 */
public class AbstractUpdateTests extends TestCase {

    @Test
    public void testTest() throws ProblemLoaderException {
        KeYEnvironment<DefaultUserInterfaceControl> env = //
                HelperClassForTests.createKeYEnvironment();
        assertNotNull(env);
    }

}
