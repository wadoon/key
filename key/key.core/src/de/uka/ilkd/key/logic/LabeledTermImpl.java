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

package de.uka.ilkd.key.logic;

import org.key_project.common.core.logic.CCLabeledTermImpl;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.SourceElement;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
class LabeledTermImpl extends CCLabeledTermImpl<SourceElement, JavaBlock, Visitor, Term> implements Term {

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
            JavaBlock javaBlock, ImmutableArray<TermLabel> labels) {
        super(op, sort, subs, boundVars, javaBlock, labels);
    }

    @Override
    protected ImmutableArray<Term> emptyTermList() {
        return TermImpl.EMPTY_TERM_LIST;
    }

    @Override
    protected JavaBlock emptyModalContent() {
        return JavaBlock.EMPTY_JAVABLOCK;
    }

}
