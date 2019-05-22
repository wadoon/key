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

package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Optional;
import java.util.function.Predicate;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;

/**
 * Term transformer for linking a termination specifier in the context of
 * abstract execution to its precondition, and for coupling its post condition
 * to it. More precisely, it creates the formula "(specifier <-> PRECONDITION) &
 * (specifier -> POSTCONDITION)", where "specifier" might be "returnFlag =
 * true", "!exc = null" etc.
 *
 * @author Dominic Steinhoefel
 */
public class RetrieveAESpecTransformer extends AbstractTermTransformer {
    private final Behavior behavior;
    private final boolean isBooleanFlag;

    public RetrieveAESpecTransformer(final String name, final Behavior behavior,
            final boolean isBooleanFlag) {
        super(new Name(name), 2);
        this.behavior = behavior;
        this.isBooleanFlag = isBooleanFlag;
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final AbstractPlaceholderStatement abstrStmt = (AbstractPlaceholderStatement) svInst
                .getInstantiation((SchemaVariable) term.sub(0).op());

        final LocationVariable flag = (LocationVariable) term.sub(1).op();

        final ImmutableSet<BlockContract> contracts = services.getSpecificationRepository()
                .getAbstractPlaceholderStatementContracts(abstrStmt);

        for (final BlockContract contract : contracts) {
            if (contract.getBaseName().contains(behavior.toString())) {
                final Term condition = isBooleanFlag ? tb.equals(tb.var(flag), tb.TRUE())
                        : tb.not(tb.equals(tb.var(flag), tb.NULL()));

                /*
                 * NOTE (DS, 2019-05-22): The mechanisms creating block contracts (which we
                 * "abuse" for AE) create an "exception variable" for post conditions as a
                 * standard, so the post condition will look like
                 * "and(equals(exc#25,null),ActualPostCondition)". We remove this first conjunct
                 * here. Alternatively, we could hook into the JMLSpecFactory or
                 * BlockContractImpl, but AE should not change the block contract
                 * implementation. Additionally, the precondition contains "measuredByEmpty",
                 * which we do not need for AE. So yes, what follows is a hack, but it works and
                 * does not change other stuff that does not know about AE.
                 */

                final Optional<Term> maybePre = Optional.ofNullable(contract.getPre(services))
                        .map(pre -> removeMeasuredByEmpty(pre, services))
                        .filter(pre -> !pre.equals(tb.tt())) //
                        .map(pre -> tb.equals(condition, pre));
                final Optional<Term> maybePost = Optional.ofNullable(contract.getPost(services))
                        .map(post -> removeExceptionVariableConjunct(post, services))
                        .filter(post -> !post.equals(tb.tt())) //
                        .map(post -> tb.imp(condition, post));

                return tb.and(maybePre.orElse(tb.tt()), maybePost.orElse(tb.tt()));
            }
        }

        return tb.tt();
    }

    private Term removeMeasuredByEmpty(Term t, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Function measuredByEmpty = (Function) services.getNamespaces()
                .lookup(new Name("measuredByEmpty"));

        return GenericTermReplacer.replace(t, //
                term -> term.op() == measuredByEmpty, sub -> tb.tt(), services);
    }

    private Term removeExceptionVariableConjunct(Term t, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Predicate<Term> filter1 = term -> term.op() == Equality.EQUALS
                && term.sub(0).op() instanceof LocationVariable
                && term.sub(0).op().name().toString().contains("#")
                && term.sub(1).sort() instanceof NullSort;
        final Predicate<Term> filter2 = term -> term.op() == Junctor.NOT
                && filter1.test(term.sub(0));

        return GenericTermReplacer.replace(t, filter2.or(filter1), sub -> tb.tt(), services);
    }

}