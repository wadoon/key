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

package de.uka.ilkd.key.abstractexecution.rule.metaconstruct;

import java.util.Optional;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;

/**
 * Term transformer for linking a completion type specifier in the context of
 * abstract execution to its precondition. More precisely, it creates the
 * formula "(specifier <-> PRECONDITION)", where "specifier" might be a term
 * like "returns_P(accessibles)".
 *
 * @author Dominic Steinhoefel
 */
public class RetrieveAEPreconditionTransformer extends AbstractTermTransformer {
    private final Behavior behavior;

    public RetrieveAEPreconditionTransformer(final String name, final Behavior behavior) {
        super(new Name(name), 2);
        this.behavior = behavior;
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            GoalLocalSpecificationRepository localSpecRepo, Services services) {
        final Optional<ExecutionContext> executionContext = Optional
                .ofNullable(svInst.getExecutionContext());

        final TermBuilder tb = services.getTermBuilder();

        final AbstractProgramElement ape = (AbstractProgramElement) svInst
                .getInstantiation((SchemaVariable) term.sub(0).op());

        final LocationVariable flag = (LocationVariable) term.sub(1).op();

        final ImmutableSet<BlockContract> contracts = localSpecRepo
                .getAbstractProgramElementContracts(ape);

        for (final BlockContract contract : contracts) {
            if (contract.getBaseName().contains(behavior.toString())) {
                final Term condition = tb.equals(tb.var(flag), tb.TRUE());
                final Optional<Term> maybePre = Optional.ofNullable(contract.getPre(services))
                        .filter(pre -> !pre.equals(tb.tt())) //
                        .map(pre -> AbstractUpdateFactory.normalizeSelfVarInTerm(pre,
                                executionContext, services))
                        .map(pre -> tb.equals(condition, pre));

                return maybePre.orElse(tb.tt());
            }
        }

        return tb.tt();
    }

}