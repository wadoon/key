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

package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.SymbExOnlyStrategy;

public class SymbExOnlyMacro extends StrategyProofMacro {

    private static final Name NON_HUMAN_INTERACTION_RULESET = new Name("notHumanReadable");

    @Override
    public String getName() {
        return "Symbolic Execution Only";
    }

    @Override
    public String getCategory() {
        return "Auto Pilot";
    }

    @Override
    public String getScriptCommandName() {
        return "symbExOnly";
    }

    @Override
    public String getDescription() {
        return "Perform only symbolic execution (in particular, no further simplifications)";
    }

    static boolean hasModality(Node node) {
        Sequent sequent = node.sequent();
        for (SequentFormula sequentFormula : sequent) {
            if(hasModality(sequentFormula.formula())) {
                return true;
            }
        }

        return false;
    }

    private static boolean hasModality(Term term) {
        if(term.containsLabel(ParameterlessTermLabel.SELF_COMPOSITION_LABEL)) {
            // ignore self composition terms
            return false;
        }

        if(term.op() instanceof Modality) {
            return true;
        }

        for (Term sub : term.subs()) {
            if(hasModality(sub)) {
                return true;
            }
        }

        return false;
    }

    /**
     * Checks if a rule is marked as not suited for interaction.
     *
     * @param rule
     */
    static boolean isNonHumanInteractionTagged(Rule rule) {
        return isInRuleSet(rule, NON_HUMAN_INTERACTION_RULESET);
    }

    private static boolean isInRuleSet(Rule rule, Name ruleSetName) {
        if (rule instanceof Taclet) {
            Taclet taclet = (Taclet) rule;
            for (RuleSet rs : taclet.getRuleSets()) {
                if (ruleSetName.equals(rs.name()))
                    return true;
            }
        }
        return false;
    }

    @Override
    protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        return new FilterSymbexStrategy(new SymbExOnlyStrategy(proof, proof.getSettings().getStrategySettings().getActiveStrategyProperties()));
    }

    /**
     * The Class FilterAppManager is a special strategy assigning to any rule
     * infinite costs if the goal has no modality
     */
    private static class FilterSymbexStrategy extends FilterStrategy {

        private static final Name NAME = new Name(FilterSymbexStrategy.class.getSimpleName());

        public FilterSymbexStrategy(Strategy delegate) {
            super(delegate);
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            if(!hasModality(goal.node())) {
                return false;
            }
            if(isNonHumanInteractionTagged(app.rule())) {
                return false;
            }

            return super.isApprovedApp(app, pio, goal);
        }

      @Override
      public boolean isStopAtFirstNonCloseableGoal() {
         return false;
      }

    }

}
