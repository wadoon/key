package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.function.Function;

public class RememberRule implements BuiltInRule {

    public static final Name NAME = new Name("Remember and close");
    public static final RememberRule INSTANCE = new RememberRule();

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        return pio != null && pio.isTopLevel();
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new RememberRuleApp(this, pos);
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) throws RuleAbortException {
        if (!findOnOtherSide(goal, services, ruleApp)) {
            // throw new RuleAbortException("The formula has not occurred yet!");
            return ImmutableSLList.<Goal>nil().prepend(goal);
        } else {
            return ImmutableSLList.nil();
        }
    }

    private boolean findOnOtherSide(Goal goal, Services services, RuleApp ruleApp) {
        PosInOccurrence pio = ruleApp.posInOccurrence();
        Term formula = pio.sequentFormula().formula();

        // select the opposite side
        Function<Sequent, Semisequent> sideSelector =
                pio.isInAntec() ? x -> x.succedent() : x -> x.antecedent();

        Node node = goal.node();
        while(node != null) {
            for (SequentFormula sequentFormula : sideSelector.apply(node.sequent())) {
                if(sequentFormula.formula().equalsModRenaming(formula)) {
                    return true;
                }
            }
            node = node.parent();
        }

        return false;
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public String displayName() {
        return NAME.toString();
    }

    @Override
    public String toString() {
        return displayName();
    }
}
