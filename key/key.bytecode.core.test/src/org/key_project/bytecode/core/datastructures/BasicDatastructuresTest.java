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
import org.key_project.bytecode.core.logic.calculus.*;
import org.key_project.bytecode.core.logic.factories.TermBuilder;
import org.key_project.bytecode.core.logic.op.LocationVariable;
import org.key_project.bytecode.core.services.TermServicesImpl;
import org.key_project.bytecode.core.services.TheoryServices;
import org.key_project.common.core.logic.Name;
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
    private static final Sort INT_SORT = new SortImpl(new Name("int"));
    private static final TermBuilder TB = TermServicesImpl.instance()
            .getTermBuilder();
    private static final SortedType INT_TYPE = new IntType();

    @Test
    public void testSimpleBytecodeSequentCreation() {

        TermServicesImpl.instance().getNamespaces().sorts().add(INT_SORT);
        TheoryServices theories = new TheoryServices(
                TermServicesImpl.instance());
        
        LocationVariable i = new LocationVariable(new Name("i"), INT_TYPE); //TODO type
        Term iTerm = TB.var(i);

        LinkedList<Instruction> insns = new LinkedList<Instruction>();

        // insns.add(...)

        InstructionBlock program = new InstructionBlock(insns);

        Term anteForm =
                TB.equals(iTerm, theories.getIntegerTheory().zero());

        Term succForm =
                TB.prog(Modality.DIA, program,
                        TB.equals(iTerm, theories.getIntegerTheory()
                                .one()));

        Semisequent ante =
                new SemisequentImpl(ImmutableSLList.<SequentFormula> nil()
                        .prepend(new SequentFormula(anteForm)));
        Semisequent succ =
                new SemisequentImpl(ImmutableSLList.<SequentFormula> nil()
                        .prepend(new SequentFormula(succForm)));
        Sequent seq = SequentImpl.createSequent(ante, succ);

        assertNotNull(seq);
        
    }
    
    private static class IntType implements SortedType {
        @Override
        public String getName() {
            return "int";
        }
        
        @Override
        public String getFullName() {
            return getName();
        }
        
        @Override
        public Sort getSort() {
            return INT_SORT;
        }
    }

}
