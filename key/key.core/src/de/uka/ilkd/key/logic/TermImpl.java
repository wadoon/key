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

package de.uka.ilkd.key.logic;

import org.key_project.common.core.logic.CCTermImpl;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.SourceElement;

/**
 * The currently only class implementing the Term interface. TermFactory should
 * be the only class dealing directly with the TermImpl class.
 */
class TermImpl extends CCTermImpl<SourceElement, JavaBlock, Visitor, Term>
        implements Term {

    static final ImmutableArray<Term> EMPTY_TERM_LIST =
            new ImmutableArray<Term>();

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public TermImpl(Operator op, Sort sort, ImmutableArray<Term> subs,
            ImmutableArray<QuantifiableVariable> boundVars, JavaBlock javaBlock) {
        super(op, sort, subs, boundVars, javaBlock);
    }

    // -------------------------------------------------------------------------
    // implementation of inherited abstract methods
    // -------------------------------------------------------------------------

    @Override
    protected ImmutableArray<Term> emptyTermList() {
        return EMPTY_TERM_LIST;
    }

    @Override
    protected JavaBlock emptyModalContent() {
        return JavaBlock.EMPTY_JAVABLOCK;
    }

}
