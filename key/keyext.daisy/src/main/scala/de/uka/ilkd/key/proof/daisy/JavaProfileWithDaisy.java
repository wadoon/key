package de.uka.ilkd.key.proof.daisy;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.FilterStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.DefaultProfileResolver;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.JavaCardDLStrategyFactory;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Immutables;

import java.util.Arrays;


public class JavaProfileWithDaisy extends JavaProfile {

    private static final JavaProfileWithDaisy INSTANCE = new JavaProfileWithDaisy();
    public static final Name STRATEGY_NAME = new Name("Daisy-aware Strategy");
    public static final DaisyStrategyFactory DAISY_STRATEGY_FACTORY = new DaisyStrategyFactory();

    public static class Resolver implements DefaultProfileResolver {

        @Override
        public String getProfileName() {
            return "Java Profile for Daisy";
        }

        @Override
        public Profile getDefaultProfile() {
            return INSTANCE;
        }
    }


    private static class DaisyStrategyFactory extends JavaCardDLStrategyFactory {
        @Override
        public Strategy create(Proof proof, StrategyProperties strategyProperties) {
           Strategy superRes = super.create(proof, strategyProperties);
           FilterStrategy filterStrategy = new FilterStrategy(superRes) {
               @Override
               public boolean isStopAtFirstNonCloseableGoal() {
                   return false;
               }

               @Override
               public Name name() {
                   return STRATEGY_NAME;
               }

               @Override
               public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {
                   if(app.rule() instanceof DaisyBoundsBuiltinRule) {
                       return TopRuleAppCost.INSTANCE;
                   }
                   return super.computeCost(app, pio, goal);
               }
           };
           return filterStrategy;
        }

        @Override
        public Name name() {
            return STRATEGY_NAME;
        }
    }

    @Override
    public StrategyFactory getDefaultStrategyFactory() {
        return DAISY_STRATEGY_FACTORY;
    }

    @Override
    protected ImmutableList<BuiltInRule> initBuiltInRules() {
        ImmutableList<BuiltInRule> result =
                ImmutableSLList.<BuiltInRule>nil().
                        prepend(DaisyBoundsBuiltinRule.INSTANCE);
        result = result.prepend(super.initBuiltInRules());
        return result;
    }
}
