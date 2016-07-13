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
import org.key_project.bytecode.core.bytecode.abstraction.PrimitiveType;
import org.key_project.bytecode.core.bytecode.instructions.IConst;
import org.key_project.bytecode.core.bytecode.operands.IntOperand;
import org.key_project.bytecode.core.logic.InstructionBlock;
import org.key_project.bytecode.core.logic.Term;
import org.key_project.bytecode.core.logic.calculus.Semisequent;
import org.key_project.bytecode.core.logic.calculus.SemisequentImpl;
import org.key_project.bytecode.core.logic.calculus.Sequent;
import org.key_project.bytecode.core.logic.calculus.SequentImpl;
import org.key_project.bytecode.core.logic.factories.TermBuilder;
import org.key_project.bytecode.core.logic.op.LocationVariable;
import org.key_project.bytecode.core.services.BCTermServices;
import org.key_project.bytecode.core.services.TermServicesImpl;
import org.key_project.bytecode.core.services.TheoryServices;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Namespace;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.Modality;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.logic.sort.SortImpl;
import org.key_project.common.core.program.abstraction.SortedType;
import org.key_project.util.collection.ImmutableSLList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class BasicDatastructuresTest extends TestCase {
    private final Sort intSort;
    private final TermBuilder tb;
    private final SortedType intType;
    private final BCTermServices termServices;

    public BasicDatastructuresTest() {
        intSort = new SortImpl(new Name("int"));
        termServices = new TermServicesImpl();
        tb = termServices.getTermBuilder();
        intType = PrimitiveType.JAVA_INT;
    }

    @Test
    public void testSimpleBytecodeSequentCreation() {

        termServices.getNamespaces().sorts().add(intSort);

        Namespace funcNS = termServices.getNamespaces().functions();
        funcNS.addSafely(new Function(new Name("#"), intSort));
        funcNS.addSafely(new Function(new Name("0"), intSort));
        funcNS.addSafely(new Function(new Name("1"), intSort));
        // ... have to add all int functions or read them in from a KeY file!

        TheoryServices theories = new TheoryServices(termServices);

        LocationVariable i = new LocationVariable(new Name("i"), intType);
        Term iTerm = tb.var(i);

        LinkedList<Instruction> insns = new LinkedList<Instruction>();

        insns.add(new IConst(new IntOperand(theories.getIntegerTheory()
                .one())));

        InstructionBlock program = new InstructionBlock(insns);

        Term anteForm =
                tb.equals(iTerm, theories.getIntegerTheory().zero());

        Term succForm =
                tb.prog(Modality.DIA, program,
                        tb.equals(iTerm, theories.getIntegerTheory()
                                .one()));

        Semisequent ante =
                new SemisequentImpl(ImmutableSLList
                        .<SequentFormula<Term>>nil()
                        .prepend(new SequentFormula<Term>(anteForm)));
        Semisequent succ =
                new SemisequentImpl(ImmutableSLList
                        .<SequentFormula<Term>>nil()
                        .prepend(new SequentFormula<Term>(succForm)));
        Sequent seq = SequentImpl.createSequent(ante, succ);

        assertNotNull(seq);

    }

}
