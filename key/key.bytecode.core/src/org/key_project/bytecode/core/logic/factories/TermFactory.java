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

package org.key_project.bytecode.core.logic.factories;

import java.util.Map;

import org.key_project.bytecode.core.logic.*;
import org.key_project.common.core.logic.factories.CCTermFactoryImpl;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.op.TypeCheckingAndInferenceService;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class TermFactory extends CCTermFactoryImpl<InstructionBlock, Term> {

    /**
     * TODO: Document.
     *
     * @param cache
     * @param clazz
     */
    public TermFactory(Map<Term, Term> cache) {
        super(cache, Term.class);
    }
    
    @Override
    protected Term doCreateTerm(Operator op, ImmutableArray<Term> subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            InstructionBlock javaBlock, ImmutableArray<TermLabel> labels) {
        final Sort sort =
                new TypeCheckingAndInferenceServiceImpl<Operator>().sort(
                        subs, op);

        final Term newTerm =
                (labels == null || labels.isEmpty() ?
                        new TermImpl(op, sort, subs, boundVars, javaBlock) :
                        new LabeledTermImpl(op, sort, subs, boundVars,
                                javaBlock, labels));

        return newTerm;
    }

    @Override
    protected <O extends Operator> TypeCheckingAndInferenceService<O> getTypeCheckingAndInferenceService(
            O op) {
        return new TypeCheckingAndInferenceServiceImpl<O>();
    }

}
