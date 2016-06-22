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

import java.util.Map;

import org.key_project.common.core.logic.factories.CCTermFactory;
import org.key_project.common.core.logic.factories.CCTermFactoryImpl;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.op.TypeCheckingAndInferenceService;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.op.TypeCheckingAndInferenceServiceImpl;

/**
 * The TermFactory is the <em>only</em> way to create terms using constructors
 * of class Term or any of its subclasses. It is the only class that implements
 * and may exploit knowledge about sub classes of {@link Term}. All other
 * classes of the system only know about terms what the {@link Term} class
 * offers them.
 * 
 * This class is used to encapsulate knowledge about the internal term
 * structures. See {@link de.uka.ilkd.key.logic.TermBuilder} for more convenient
 * methods to create terms.
 */
public final class TermFactory extends CCTermFactoryImpl<JavaBlock, Term>
        implements CCTermFactory<JavaBlock, Term> {

    static final ImmutableArray<Term> NO_SUBTERMS =
            new ImmutableArray<Term>();

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public TermFactory(Map<Term, Term> cache) {
        super(cache);
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    protected ImmutableArray<Term> emptyTermList() {
        return NO_SUBTERMS;
    }

    @Override
    protected Term doCreateTerm(Operator op, ImmutableArray<Term> subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            JavaBlock javaBlock, ImmutableArray<TermLabel> labels) {
        final Sort sort =
                TypeCheckingAndInferenceServiceImpl.getTypeCheckerFor(op).sort(
                        subs, op);

        final Term newTerm =
                (labels == null || labels.isEmpty() ?
                        new TermImpl(op, sort, subs, boundVars, javaBlock) :
                        new LabeledTermImpl(op, sort, subs, boundVars,
                                javaBlock, labels));

        return cacheTerm(newTerm);
    }

    @Override
    public Term[] createTermArray(int size) {
        return new Term[size];
    }

    @Override
    public Term[] createTermArray(Term sub1) {
        return new Term[] { sub1 };
    }

    @Override
    public Term[] createTermArray(Term sub1, Term sub2) {
        return new Term[] { sub1, sub2 };
    }

    @Override
    public Term[] createTermArray(Term sub1, Term sub2, Term sub3) {
        return new Term[] { sub1, sub2, sub3 };
    }

    @Override
    protected <O extends Operator> TypeCheckingAndInferenceService<O> getTypeCheckingAndInferenceService(
            O op) {
        return TypeCheckingAndInferenceServiceImpl.getTypeCheckerFor(op);
    }

    // -------------------------------------------------------------------------
    // private interface
    // -------------------------------------------------------------------------

}
