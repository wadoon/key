package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.rulefilter.RulesetFilter;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.AbstractFeatureStrategy;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;
import de.uka.ilkd.key.strategy.feature.ConditionalFeature;
import de.uka.ilkd.key.strategy.feature.Feature;

public class JavaIntRemovingStrategy extends AbstractFeatureStrategy {
	
	public static class JavaIntRemovingStrategyFactory implements StrategyFactory {

	      /**
	       * {@inheritDoc}
	       */
	      @Override
	      public Strategy create(Proof proof, StrategyProperties sp) {
	         return new JavaIntRemovingStrategy(proof);
	      }

	      /**
	       * {@inheritDoc}
	       */
	      @Override
	      public Name name() {
	         return NAME;
	      }

	      /**
	       * {@inheritDoc}
	       */
	      @Override
	      public StrategySettingsDefinition getSettingsDefinition() {
	         return JavaProfile.DEFAULT.getSettingsDefinition();
	      }

	}

	public final static Name NAME = new Name("Java Integer Function Removal");
	private final RulesetFilter onlyIntSemantics;
	private final Feature belongsToJavaIntegerSemantics;
	
	public JavaIntRemovingStrategy(Proof p_proof) {
		super(p_proof);
		onlyIntSemantics = new RulesetFilter(new Name("javaIntegerSemantics"));
		belongsToJavaIntegerSemantics = ConditionalFeature.createConditional(onlyIntSemantics, longConst(-1000), TopRuleAppCost.INSTANCE);
	}


	@Override
	public boolean isStopAtFirstNonCloseableGoal() {
		return false;
	}

	@Override
	public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {
		return belongsToJavaIntegerSemantics.compute(app, pio, goal);
	}

	@Override
	public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
		return onlyIntSemantics.filter(app.rule());
	}

	@Override
	public Name name() {
		return NAME;
	}

	@Override
	protected RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio,
			Goal goal) {
		return TopRuleAppCost.INSTANCE;
	}
}
