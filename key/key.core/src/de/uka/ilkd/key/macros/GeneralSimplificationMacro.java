package de.uka.ilkd.key.macros;

import java.util.LinkedHashSet;
import java.util.Set;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.*;

/**
 * This macro applies only simplification rules. The idea is to use it instead
 * of the {@link OneStepSimplifier}.
 *
 * @author Dominic Steinhoefel
 */
public class GeneralSimplificationMacro extends
        AbstractPropositionalExpansionMacro {

    /**
     * Name for this {@link ProofMacro}.
     */
    public static final String SIMPLIFICATION_ONLY =
            "Simplification Only";

    /**
     * The sets of {@link Rule}s that should be activated by this
     * {@link ProofMacro}.
     */
    private static final ImmutableList<String> RULE_SETS =
            ImmutableSLList.<String> nil() //
                    .append("concrete")
                    .append("update_elim")
                    .append("update_apply_on_update")
                    .append("update_apply")
                    .append("update_join")
                    .append("elimQuantifier");

    /**
     * {@link Rule} sets that should explicitely be excluded.
     */
    private static final ImmutableList<String> EXCLUDED_RULE_SETS =
            ImmutableSLList.<String> nil();

    @Override
    public String getName() {
        return SIMPLIFICATION_ONLY;
    }

    @Override
    public String getCategory() {
        return "Simplification";
    }

    @Override
    public String getScriptCommandName() {
        return "simp";
    }

    @Override
    public String getDescription() {
        return "Applies only simplification rules";
    }

    @Override
    protected Set<String> getAdmittedRuleNames(final Proof proof) {
        assert !proof.openGoals().isEmpty();
        final Set<String> result = new LinkedHashSet<>();

        // collect apps present in all open goals
        final Set<NoPosTacletApp> allApps =
                proof.openGoals().head().ruleAppIndex()
                        .tacletIndex().allNoPosTacletApps();

        for (final Goal goal : proof.openGoals().tail()) {
            allApps.retainAll(goal.ruleAppIndex()
                    .tacletIndex()
                    .allNoPosTacletApps());
        }

        for (final NoPosTacletApp app : allApps) {
            final Taclet tac = app.taclet();
            if (!(tac instanceof RewriteTaclet)
                    || !tac.hasReplaceWith()
                    || !tac.ifSequent().isEmpty()
                    || tac.goalTemplates().size() != 1
                    || !tac.goalTemplates().head().sequent().isEmpty()
                    || !tac.varsNew().isEmpty()
                    || !tac.varsNewDependingOn().isEmpty()
                    || ((RewriteTaclet) tac)
                            .getApplicationRestriction() != RewriteTaclet.NONE
                    || !proof.getInitConfig().getJustifInfo()
                            .getJustification(tac).isAxiomJustification()) {
                continue;
            }

            boolean accept = false;
            for (final String ruleSetName : RULE_SETS) {
                for (RuleSet rs : app.taclet().getRuleSets()) {
                    if (rs.name().toString().equals(ruleSetName)) {
                        accept = true;
                    } else if (EXCLUDED_RULE_SETS
                            .contains(rs.name().toString())) {
                        accept = false;
                        break;
                    }
                }
            }

            if (accept) {
                result.add(tac.name().toString());
            }
        }

        return result;
    }

    @Override
    protected boolean allowOSS() {
        return false;
    }

}
