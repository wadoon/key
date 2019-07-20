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

import de.uka.ilkd.key.util.removegenerics.*;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@Suite.SuiteClasses({
        TestMultipleBounds.class,
        TestTypeReference.class,
        TestTypeReference.class,
        TestMemberReference.class,
        TestMethodDeclaration.class,
        TestClassDeclaration.class
})
@RunWith(Suite.class)
public class AllTests {
}