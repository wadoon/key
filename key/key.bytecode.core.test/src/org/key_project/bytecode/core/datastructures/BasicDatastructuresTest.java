// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.bytecode.core.datastructures;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.bytecode.core.logic.calculus.*;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.logic.sort.SortImpl;
import org.key_project.util.collection.ImmutableSLList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class BasicDatastructuresTest extends TestCase {
    private static final Sort INT_SORT = new SortImpl(new Name("int"));

    @Test
    public void testSimpleBytecodeSequentCreation() {
        Semisequent ante =
                new SemisequentImpl(ImmutableSLList.<SequentFormula> nil());
        Semisequent succ = new SemisequentImpl(null);
        Sequent seq = SequentImpl.createSequent(ante, succ);
        
        assertNotNull(seq);
    }

}
