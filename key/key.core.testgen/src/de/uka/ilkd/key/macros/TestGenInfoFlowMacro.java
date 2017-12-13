package de.uka.ilkd.key.macros;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.Strategy;

/**
 * Macro for test generation which perform double symbolic execution 
 * (include loop unwinding for multiple loops).
 * @author Muessig
 *
 */
public class TestGenInfoFlowMacro extends StrategyProofMacro {
	
	private static class TestGenInfoFlowStrategy extends FilterStrategy{

		private static final Name NAME = new Name(
		        TestGenInfoFlowStrategy.class.getSimpleName());
		private static final Set<String> unwindRules;
		private static final int UNWIND_COST = 1000;
		private static final String IFSPLIT= "ifSplit";
		private final int limitPerLoop;
		private static boolean belongsToUnwind = false;
		
		
		static {
			unwindRules = new HashSet<String>();
			TestGenInfoFlowStrategy.unwindRules.add("loopUnwind");
			TestGenInfoFlowStrategy.unwindRules.add("doWhileUnwind");
			TestGenInfoFlowStrategy.unwindRules.add("methodCall");
			TestGenInfoFlowStrategy.unwindRules.add("methodCallWithAssignment");
			TestGenInfoFlowStrategy.unwindRules.add("staticMethodCall");
			TestGenInfoFlowStrategy.unwindRules.add("staticMethodCallWithAssignment");
		}

		private static boolean isUnwindRule(Rule rule) {
			if (rule == null) {
				return false;
			}
			final String name = rule.name().toString();
			return TestGenInfoFlowStrategy.unwindRules.contains(name);
		}

		public TestGenInfoFlowStrategy(Strategy delegate) {
			super(delegate);
			limitPerLoop = ProofIndependentSettings.DEFAULT_INSTANCE
			        .getTestGenerationSettings().getMaximalUnwinds();
		}

		@Override
		public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio,
		        Goal goal) {
			if (TestGenInfoFlowStrategy.isUnwindRule(app.rule())) {
				return NumberRuleAppCost.create(TestGenInfoFlowStrategy.UNWIND_COST);
			}
			return super.computeCost(app, pio, goal);
		}
		
		/**
		 * check if the applied rule of the node is a "ifsplit" rule
		 * @param node the node you want to check
		 * @return true if the applied rule is "ifSplit"
		 */
		private boolean isIfSplitRule(Node node) {
			if (node.getAppliedRuleApp().rule().name().toString().equals(IFSPLIT)) {
				return true;
			}
			return false;
		}
		
		/**
		 * this method count the number of unwind rules for the current loop. 
		 * @param goal the current goal
		 * @return the number of unwind rules used for the current loop
		 */
		private int computeUnwindRules(Goal goal) {
			int unwindings = 0;
			Node prevNode = goal.node();
			Node currentNode = goal.node();
			while(!currentNode.root()) {
				final RuleApp app = currentNode.getAppliedRuleApp();
				if (app != null) {
					if (isUnwindRule(app.rule())) {
						//TODO Save loop signature and count for each loop
						
						//count unwindings used for this loop
						++unwindings;
						
					}
				}
				prevNode = currentNode;
				currentNode = currentNode.parent();
				
				if (!currentNode.root()) {
					//check if the applied rule is if split and belongs to an unwind rule
					if (isIfSplitRule(currentNode)) {
						
						belongsToUnwind = false;
						
						//check if the current ifSplit rule belongs to an unwinding rule 
						Node checkNode = currentNode.parent();
						while(!checkNode.root()) {
							RuleApp appIfSplit = checkNode.getAppliedRuleApp();
							if(isIfSplitRule(checkNode)) {
								break;
								//last if split does not belong to unwind rule
							}
							if(isUnwindRule(appIfSplit.rule())) {
								//the current ifSplitNode belongs to the unwinding rule
								belongsToUnwind = true;
								break;
							}
							checkNode = checkNode.parent();
						}
						
						if(belongsToUnwind) {
							// if left child node, stop count (unwinding rules above are part of other loops)
							if(currentNode.child(1).equals(prevNode)) {
								break;
							}
						}
						
					}
				}
			}
			return unwindings;
		}
		
		@Override
		public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
			
			if (!TestGenInfoFlowMacro.hasModality(goal.node())) {
				return false;
			}
			
			if (TestGenInfoFlowStrategy.isUnwindRule(app.rule())) {
				
				int unwindings = computeUnwindRules(goal);
				//check the number of unwindings for the current loop
				if (unwindings >= limitPerLoop) {
					return false;
				} else {
					return true;
				}
			} else {
				return super.isApprovedApp(app, pio, goal);
			}
			
		}
		



		@Override
		public Name name() {
			return TestGenInfoFlowStrategy.NAME;
		}

      @Override
      public boolean isStopAtFirstNonCloseableGoal() {
         return false;
      }
	}
	
	/*
	 * find a modality term in a node
	 */
	private static boolean hasModality(Node node) {
		final Sequent sequent = node.sequent();
		for (final SequentFormula sequentFormula : sequent) {
			if (TestGenInfoFlowMacro.hasModality(sequentFormula.formula())) {
				return true;
			}
		}
		return false;
	}

	/*
	 * recursively descent into the term to detect a modality.
	 */
	private static boolean hasModality(Term term) {
		if (term.op() instanceof Modality) {
			return true;
		}
		for (final Term sub : term.subs()) {
			if (TestGenInfoFlowMacro.hasModality(sub)) {
				return true;
			}
		}
		return false;
	}
	

	public String getName() {
		return "TestGen (multiple finite loop unwinding for double symbolic execution)";
	}

	@Override
	public String getCategory() {
		// TODO Auto-generated method stub
		
		return null;
	}

	@Override
	public String getDescription() {
		return "Finish symbolic execution with multiple restrict loop unwindings.";
	}

	@Override
	protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
		return new TestGenInfoFlowStrategy(proof
		        .getActiveStrategy());
	}

}
