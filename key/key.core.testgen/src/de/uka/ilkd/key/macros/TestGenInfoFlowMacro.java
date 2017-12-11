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
		private int limitPerLoop;
		
		
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
						//count unwindings used for this loop
						++unwindings;
					}
				}
				prevNode = currentNode;
				currentNode = currentNode.parent();
				if (!currentNode.root()) {
					if (currentNode.getAppliedRuleApp().rule().name().toString().equals("ifSplit")) {
						//TODO test ifsplit belongs to unwind rule 
						
						//System.out.println(currentNode.getAppliedRuleApp().rule().name().toString() + " " + currentNode.serialNr());
						
						// if left child node, stop count (unwinding rules above are part of other loops)
						if(currentNode.child(1).equals(prevNode)) {
							break;
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
