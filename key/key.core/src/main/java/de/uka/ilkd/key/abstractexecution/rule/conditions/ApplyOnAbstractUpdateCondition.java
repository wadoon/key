// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.abstractexecution.rule.conditions;

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.ParametricSkolemLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Variable condition for applying an update on an abstract update:
 * <code>{U}U_P(assgn:=access} -->
 * U_P(assgn:={U}access}</code>
 *
 * @author Dominic Steinhoefel
 */
public final class ApplyOnAbstractUpdateCondition implements VariableCondition {
    private final UpdateSV u1SV;
    private final UpdateSV u2SV;
    private final UpdateSV resultSV;

    public ApplyOnAbstractUpdateCondition(UpdateSV uSV, UpdateSV u2SV, UpdateSV resultSV) {
        this.u1SV = uSV;
        this.u2SV = u2SV;
        this.resultSV = resultSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate, MatchConditions mc,
            Goal goal, Services services) {
        final SVInstantiations svInst = mc.getInstantiations();
        final TermBuilder tb = services.getTermBuilder();

        final Term u1 = (Term) svInst.getInstantiation(u1SV);
        final Term u2 = (Term) svInst.getInstantiation(u2SV);
        final Term origResult = (Term) svInst.getInstantiation(resultSV);

        if (u1 == null || u2 == null || !(u2.op() instanceof AbstractUpdate)) {
            return null;
        }

        if (origResult != null) {
            return mc;
        }

        /* non_final */ AbstractUpdate abstrUpd = (AbstractUpdate) u2.op();

        final Term[] args = u2.subs().stream().map(sub -> tb.apply(u1, sub))
                .collect(Collectors.toList()).toArray(new Term[0]);

        // Special case: Abstract update with parametric location set

        final Optional<Map<AbstractUpdateLoc, AbstractUpdateLoc>> changedAssgn = //
                handleLocSetFamilies(tb, u1, abstrUpd);

        if (!changedAssgn.isPresent()) {
            return null;
        }

        if (!changedAssgn.get().isEmpty()) {
            abstrUpd = services.abstractUpdateFactory().changeAssignables( //
                    abstrUpd, changedAssgn.get());
        }

        return mc.setInstantiations(
                svInst.add(resultSV, tb.abstractUpdate(abstrUpd, args), services));
    }

    /**
     * @param tb
     * @param updToApply
     * @param abstrUpd
     * @param changedAssgn
     */
    private Optional<Map<AbstractUpdateLoc, AbstractUpdateLoc>> handleLocSetFamilies(
            final TermBuilder tb, final Term updToApply, AbstractUpdate abstrUpd) {
        final Map<AbstractUpdateLoc, AbstractUpdateLoc> result = new LinkedHashMap<>();
        final List<ParametricSkolemLoc> paramLocs = AbstractExecutionUtils.unwrapHasTos(abstrUpd)
                .stream().filter(ParametricSkolemLoc.class::isInstance) //
                .map(ParametricSkolemLoc.class::cast) //
                .filter(loc -> Arrays.stream(loc.getParams()).map(Term::op)
                        .anyMatch(LocationVariable.class::isInstance))
                .collect(Collectors.toList());
        if (!paramLocs.isEmpty()) {
            // Need an update in PNF for that
            if (!MergeRuleUtils.isUpdateNormalForm(updToApply, true)) {
                return Optional.empty();
            }

            final Set<LocationVariable> processedVars = new HashSet<>();

            final List<Term> elems = MergeRuleUtils.getElementaryUpdates(updToApply, false, tb);
            for (int i = elems.size() - 1; i >= 0; i--) {
                final Term elemUpd = elems.get(i);

                if (elemUpd.op() instanceof AbstractUpdate) {
                    /*
                     * In many cases, there are other simplification steps which can and should be
                     * applied before applying an abstract update to an abstract update with a
                     * parametric location set. If there are no such further steps possible, then
                     * the application will most likely (maybe always) be unsound. So we don't
                     * permit it.
                     */
                    return Optional.empty();
                }

                assert elemUpd.op() instanceof ElementaryUpdate;

                final LocationVariable lv = //
                        (LocationVariable) ((ElementaryUpdate) elemUpd.op()).lhs();

                if (processedVars.contains(lv)) {
                    continue;
                }

                for (final ParametricSkolemLoc relevantParamLoc : paramLocs.stream()
                        .filter(loc -> Arrays.stream(loc.getParams()).anyMatch(t -> t.op() == lv))
                        .collect(Collectors.toList())) {
                    processedVars.add(lv);

                    final ParametricSkolemLoc newParametricSkolemLoc = new ParametricSkolemLoc(
                            relevantParamLoc.getSkFunc(),
                            Arrays.stream(relevantParamLoc.getParams())
                                    .map(loc -> loc.op() == lv ? elemUpd.sub(0) : loc)
                                    .toArray(Term[]::new));

                    final boolean isHasTo = abstrUpd.getHasToAssignables()
                            .contains(relevantParamLoc);

                    final AbstractUpdateLoc toReplace = isHasTo
                            ? new HasToLoc<ParametricSkolemLoc>(relevantParamLoc)
                            : relevantParamLoc;
                    final AbstractUpdateLoc replaceWith = isHasTo
                            ? new HasToLoc<ParametricSkolemLoc>(newParametricSkolemLoc)
                            : newParametricSkolemLoc;

                    result.put(toReplace, replaceWith);
                }
            }
        }

        return Optional.of(result);
    }

    @Override
    public String toString() {
        return String.format("\\applyConcreteOnAbstractUpdate(%s, %s, %s)", u1SV, u2SV, resultSV);
    }

}