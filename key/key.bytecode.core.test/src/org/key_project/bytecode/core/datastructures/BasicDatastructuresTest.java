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

import java.util.LinkedList;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.bytecode.core.bytecode.Instruction;
import org.key_project.bytecode.core.logic.InstructionBlock;
import org.key_project.bytecode.core.logic.Term;
import org.key_project.bytecode.core.logic.TermServicesImpl;
import org.key_project.bytecode.core.logic.calculus.*;
import org.key_project.bytecode.core.logic.factories.TermBuilder;
import org.key_project.common.core.ldt.IntegerTheory;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.Modality;
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
    private static final TermBuilder TB = TermServicesImpl.instance()
            .getTermBuilder();
    private static final IntegerTheory<Term> INT_THEORY = new IntegerTheory(TermServicesImpl.instance());

    @Test
    public void testSimpleBytecodeSequentCreation() {
        LinkedList<Instruction> insns = new LinkedList<Instruction>();

        // insns.add(...)

        InstructionBlock program = new InstructionBlock(insns);

        Term anteForm = TB.equals(null /* i */, null /* 0 */);

        Term succForm =
                TB.prog(Modality.DIA, program,
                        TB.equals(null /* i */, null /* 1 */));

        Semisequent ante =
                new SemisequentImpl(ImmutableSLList.<SequentFormula> nil()
                        .prepend(new SequentFormula(anteForm)));
        Semisequent succ =
                new SemisequentImpl(ImmutableSLList.<SequentFormula> nil()
                        .prepend(new SequentFormula(succForm)));
        Sequent seq = SequentImpl.createSequent(ante, succ);

        assertNotNull(seq);
    }

}
