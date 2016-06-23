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

package org.key_project.bytecode.core.logic;

import org.key_project.bytecode.core.logic.visitors.Visitor;
import org.key_project.common.core.logic.CCLabeledTermImpl;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class LabeledTermImpl extends CCLabeledTermImpl<InstructionBlock, Visitor, Term> {

    /**
     * TODO: Document.
     *
     * @param op
     * @param sort
     * @param subs
     * @param boundVars
     * @param javaBlock
     * @param labels
     */
    public LabeledTermImpl(Operator op, Sort sort, ImmutableArray<Term> subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            InstructionBlock javaBlock, ImmutableArray<TermLabel> labels) {
        super(op, sort, subs, boundVars, javaBlock, labels);
    }

    @Override
    protected ImmutableArray<Term> emptyTermList() {
        return TermImpl.EMPTY_TERM_LIST;
    }

    @Override
    protected InstructionBlock emptyModalContent() {
        return InstructionBlock.emptyBlock();
    }
}
