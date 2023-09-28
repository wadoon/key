/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tuc;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;

// TODO: sidecondition check missing,
//       but currently no mergefunction could find any constant only introduced on one branch
// TODO: pruning support (merged goals have to be unmerged and reopened)
// TODO: proof slicing?
// TODO: does KeY try to apply this rule in auto-mode? yes and it fails sometimes, because pio is null for some apps
public class TucRule implements BuiltInRule {
    public static final Logger LOGGER = LoggerFactory.getLogger(TucRuleApp.class);

    public static final TucRule INSTANCE = new TucRule();
    private static final String DISPLAY_NAME = "TUC";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    public final static Function<List<Sequent>, Pair<ImmutableList<SequentFormula>, ImmutableList<SequentFormula>>> mtn = (sequents) -> {
        if (sequents.isEmpty()) {
            return new Pair<>(ImmutableSLList.nil(), ImmutableSLList.nil());
        }
        boolean first = true;
        ImmutableList<SequentFormula> result_ante = sequents.get(0).antecedent().asList();
        for (Sequent seq2: sequents) {
            if (first) {
                first = false;
                continue;
            }
            final ImmutableList<SequentFormula> formulas = seq2.antecedent().asList();
            result_ante = result_ante.filter((phi1) -> {
                for (SequentFormula phi2: formulas) {
                    if (phi1.formula().equalsModRenaming(phi2.formula())) {
                        return true;
                    }
                }
                return false;
            });
        }
        first = true;
        ImmutableList<SequentFormula> result_succ = sequents.get(0).succedent().asList();
        for (Sequent seq2: sequents) {
            if (first) {
                first = false;
                continue;
            }
            final ImmutableList<SequentFormula> formulas = seq2.succedent().asList();
            result_succ = result_succ.filter((phi1) -> {
                for (SequentFormula phi2: formulas) {
                    if (phi1.formula().equalsModRenaming(phi2.formula())) {
                        return true;
                    }
                }
                return false;
            });
        }
        return new Pair<>(result_ante, result_succ);
    };

    @Override
    public boolean isApplicable(final Goal goal, final PosInOccurrence pio) {
        //LOGGER.debug("applicable check");
        return true;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(final PosInOccurrence pos, final TermServices services) {
        LOGGER.debug("creating tuc application with pos {}", pos);
        return new TucRuleApp(this, pos, null);
    }

    @Nonnull
    @Override
    public ImmutableList<Goal> apply(final Goal goal, final Services services, final RuleApp ruleApp) throws RuleAbortException {
        LOGGER.debug("applying tuc rule");
        if (!(ruleApp instanceof TucRuleApp app)) {
            throw new RuleAbortException("Can only apply TucRule applications");
        }
        if (app.goal != goal) {
            throw new RuleAbortException("Can only apply TucRule on the goal it was instanciated for");

        }
        if (app.formulae.first.isEmpty() && app.formulae.second.isEmpty()) {
            // TODO: leave this here?
            throw new RuleAbortException("TUC with no found formulea is equivalent to pruning, do that instead");
        }


        final ImmutableList<Goal> result = goal.split(1);
        Goal r = result.head();
        final Sequent sequent = app.ancestor.sequent();

        for (Goal g : app.mergepartners) {
            g.apply(ClosedAfterTuc.INSTANCE.createApp(goal));
        }
        r.node().setSequent(sequent);
        for (SequentFormula phi: app.formulae.first) {
            r.addFormula(phi, true, true);
        }
        for (SequentFormula phi: app.formulae.second) {
            r.addFormula(phi, false, true);
        }
        return result;
    }

    @Override
    public Name name() {
        return RULE_NAME;
    }

    @Override
    public String displayName() {
        return DISPLAY_NAME;
    }

    @Override
    public String toString() {
        return displayName();
    }
}
