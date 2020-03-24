// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.rule.metaconstruct;

import java.util.Optional;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionContractUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Returns the frame formula for an abstract program.
 * 
 * @author Dominic Steinhoefel
 */
public class GetFrameTransformer extends AbstractTermTransformer {
    private static final Name NAME = new Name("#getFrame");

    public GetFrameTransformer() {
        super(NAME, 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            GoalLocalSpecificationRepository localSpecRepo, Services services) {
        final Optional<ExecutionContext> executionContext = Optional
                .ofNullable(svInst.getExecutionContext());

        final AbstractProgramElement ape = AbstractPreconditionTransformer.getAPE(term, svInst);

        final Term frameTerm = AbstractExecutionContractUtils
                .getAccessibleAndAssignableTermsForNoBehaviorContract(ape, Optional.empty(),
                        localSpecRepo, services).second;

        return AbstractUpdateFactory.normalizeSelfVarInTerm(frameTerm, executionContext, services);
    }

}
