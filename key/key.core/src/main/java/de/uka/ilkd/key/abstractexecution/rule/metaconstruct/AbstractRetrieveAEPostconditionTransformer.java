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

import java.util.Map;
import java.util.Optional;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory.PreconditionType;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.AuxiliaryContract.Variables;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * Term transformer for linking a completion type specifier in the context of
 * abstract execution to its precondition. More precisely, it creates the
 * formula "(specifier <-> PRECONDITION)", where "specifier" might be a term
 * like "returns_P(accessibles)".
 *
 * @author Dominic Steinhoefel
 */
public class AbstractRetrieveAEPostconditionTransformer extends AbstractTermTransformer {
    private final static Map<PreconditionType, Behavior> BEHAVIOR_TYPES_MAP = new LinkedHashMap<>();

    static {
        BEHAVIOR_TYPES_MAP.put(PreconditionType.RETURN, Behavior.RETURN_BEHAVIOR);
        BEHAVIOR_TYPES_MAP.put(PreconditionType.EXC, Behavior.EXCEPTIONAL_BEHAVIOR);
        BEHAVIOR_TYPES_MAP.put(PreconditionType.NORMAL, Behavior.NORMAL_BEHAVIOR);
        BEHAVIOR_TYPES_MAP.put(PreconditionType.BREAK, Behavior.BREAK_BEHAVIOR);
        BEHAVIOR_TYPES_MAP.put(PreconditionType.CONT, Behavior.CONTINUE_BEHAVIOR);
    }

    public AbstractRetrieveAEPostconditionTransformer(Name name, int arity) {
        super(name, arity);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            GoalLocalSpecificationRepository localSpecRepo, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Operator apeSV = term.sub(0).op();
        assert apeSV instanceof ProgramSV;
        final Object apeSVInst = svInst.getInstantiation((ProgramSV) apeSV);
        assert apeSVInst instanceof AbstractProgramElement;
        final AbstractProgramElement ape = (AbstractProgramElement) apeSVInst;

        final PreconditionType preconditionType = AbstractPreconditionTransformer
                .getPreconditionType(term.sub(1), services);
        final Behavior contractType = BEHAVIOR_TYPES_MAP.get(preconditionType);
        assert contractType != null;

        final Operator returnsSV = term.sub(2).op();
        assert returnsSV instanceof LocationVariable;
        final LocationVariable returnsPV = (LocationVariable) returnsSV;

        final Operator resultSV = term.sub(3).op();
        assert resultSV instanceof LocationVariable;
        final LocationVariable resultPV = (LocationVariable) resultSV;

        final Operator excSV = term.sub(4).op();
        assert excSV instanceof LocationVariable;
        final LocationVariable excPV = (LocationVariable) excSV;

        final Optional<LocationVariable> maybeContinuesSV = term.arity() > 5
                ? Optional.of((LocationVariable) term.sub(5).op())
                : Optional.empty();

        final Optional<LocationVariable> maybeBreaksSV = term.arity() > 6
                ? Optional.of((LocationVariable) term.sub(6).op())
                : Optional.empty();

        final ImmutableSet<BlockContract> contracts = localSpecRepo
                .getAbstractProgramElementContracts(ape);

        for (final BlockContract contract : contracts) {
            if (contract.getBaseName().contains(contractType.toString())) {
                final Optional<Term> maybePost = Optional.ofNullable(contract.getPost(services))
                        .map(post -> replaceSpecialVars(post, returnsPV, resultPV, excPV,
                                maybeBreaksSV, maybeContinuesSV, contract, services))
                        .filter(post -> !post.equals(tb.tt()));

                return maybePost.orElse(tb.tt());
            }
        }

        return tb.tt();
    }

    /**
     * Replaces in <code>t</code> the occurrences of either the result variable, if
     * <code>preconditionType</code> is {@link PreconditionType#RETURN}, or the
     * exception variable, if <code>preconditionType</code> is
     * {@link PreconditionType#EXC}, by <code>pvToInsert</code>.
     * 
     * <p>
     * Returns the original {@link Term} if <code>preconditonType</code> is any
     * other type. In that case, nothing has to replaced.
     * 
     * @param t                The {@link Term} in which to replace.
     * @param returnsPV        The {@link LocationVariable} to insert instead of the
     *                         returns flag.
     * @param resultPV         The {@link LocationVariable} to insert instead of the
     *                         result flag.
     * @param excPV            The {@link LocationVariable} to insert instead of the
     *                         exc flag.
     * @param maybeBreaksSV    The {@link LocationVariable} to insert instead of the
     *                         breaks flag.
     * @param maybeContinuesSV The {@link LocationVariable} to insert instead of the
     *                         continues flag.
     * @param contract         The {@link BlockContract} for getting the placeholder
     *                         variables.
     * @param services         The {@link Services} object.
     * @return The replaced {@link Term}.
     */
    private static Term replaceSpecialVars(Term t, ProgramVariable returnsPV,
            ProgramVariable resultPV, ProgramVariable excPV,
            Optional<LocationVariable> maybeBreaksSV, Optional<LocationVariable> maybeContinuesSV,
            BlockContract contract, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Variables phVars = contract.getPlaceholderVariables();

        Term result = GenericTermReplacer
                .replace(t,
                        _t -> _t.op() == phVars.exception || _t.op() == phVars.result || _t
                                .op() == phVars.returnFlag,
                        _t -> tb.var(_t.op() == phVars.exception ? excPV
                                : (_t.op() == phVars.result ? resultPV
                                        : (_t.op() == phVars.returnFlag ? returnsPV
                                                : (ProgramVariable) _t.op()))),
                        services);

        if (maybeBreaksSV.isPresent()) {
            final LocationVariable breaksSV = maybeBreaksSV.get();
            // XXX (DS, 2019-01-31): Labeled breaks currently not supported
            assert phVars.breakFlags.size() == 1 && phVars.breakFlags.get(null) != null;
            final ProgramVariable phVar = phVars.breakFlags.get(null);
            result = GenericTermReplacer.replace( //
                    result, _t -> _t.op() == phVar, _t -> tb.var(breaksSV), services);
        }

        if (maybeContinuesSV.isPresent()) {
            final LocationVariable continuesSV = maybeContinuesSV.get();
            // XXX (DS, 2019-01-31): Labeled continues currently not supported
            assert phVars.breakFlags.size() == 1 && phVars.continueFlags.get(null) != null;
            final ProgramVariable phVar = phVars.continueFlags.get(null);
            result = GenericTermReplacer.replace( //
                    result, _t -> _t.op() == phVar, _t -> tb.var(continuesSV), services);
        }

        return result;
    }

}