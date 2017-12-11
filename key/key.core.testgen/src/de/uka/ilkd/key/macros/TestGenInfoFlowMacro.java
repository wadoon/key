package de.uka.ilkd.key.macros;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
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
 * @author Müssig
 *
 */
public class TestGenInfoFlowMacro extends StrategyProofMacro {
	
	private static class TestGenInfoFlowStrategy extends FilterStrategy{

		private static final Name NAME = new Name(
		        TestGenInfoFlowStrategy.class.getSimpleName());
		private static final Set<String> unwindRules;
		private static final int UNWIND_COST = 1000;
		private int limitPerLoop;
		
		
		static int loops = 0;
		
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
		
		
//		private int computeUnwindRules(Goal goal) {
//			
//				System.out.println("____");
//				for (RuleApp r : goal.appliedRuleApps()) {//appliedRuleApps liefert eine liste von Rules, die auf diesem Branch verwendet wurden!. Damit können wir für die verschieden Branches eine bestimmte anzahl loopunwinds zulassen! das könnte die lösung sein!
//					//System.out.println("name der regel:" +r.rule().name());
//					
//					
//					
//					if(isUnwindRule(r.rule())) {
//						limitPerLoop = limitPerLoop - 1;
//						//System.out.println("in diesem Branch wurden bereits unwind Rules verwendet");
//						//loopRulesCounter = loopRulesCounter+1;
//						//System.out.println("anzahl loopRules: "+ loopRulesCounter);
//					}
//				}
//				System.out.println("____");
//			return limitPerLoop;

//			int loopRulesCounter = 0;
//			Node node = goal.node();
//			while (!node.root()) {
//				final RuleApp app = node.getAppliedRuleApp();
//				if (app != null) {
//					final Rule rule = app.rule();
//					if (TestGenInfoFlowStrategy.isUnwindRule(rule)) {
//						for (RuleApp r : goal.appliedRuleApps()) {
//							if(isUnwindRule(r.rule())) {
//								++loopRulesCounter;
//							}
//						}
//					}
//				}
//				node = node.parent();
//			}
//			//test
//			return loopRulesCounter;
			
			
			
			//return totalUnwinds;
//		}
		
		private int computeUnwindRules(Goal goal) {
			int unwindings = 0;
			Node prevNode = goal.node();
			Node currentNode = goal.node();
			while(!currentNode.root()) {
				final RuleApp app = currentNode.getAppliedRuleApp();
				if (app != null) {
					if (isUnwindRule(app.rule())) {
						//addiere die unwindings
						++unwindings;
					}
				}
				prevNode = currentNode;
				currentNode = currentNode.parent();
				if (!currentNode.root()) {
					if (currentNode.getAppliedRuleApp().rule().name().toString().equals("ifSplit")) {
						//TODO überprüfe, ob ifSplit wirklich zu unwinding gehört
						
						//System.out.println(currentNode.getAppliedRuleApp().rule().name().toString() + " " + currentNode.serialNr());
						// falls linker Kindknoten höre hier auf zu zählen
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
				if (unwindings >= limitPerLoop) {
					return false;
				} else {
					return true;
				}
			} else {
				return super.isApprovedApp(app, pio, goal);
			}
			
		}
		

//		@Override
//		public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
//			
//			
//			
//			if (!TestGenInfoFlowMacro.hasModality(goal.node())) {
//				return false;
//			}
//			
//			
//			if (TestGenInfoFlowStrategy.isUnwindRule(app.rule())) {
//				//System.out.println("FOLGENDER NODE WURDE BEARBEITET ::::: " + goal.node().serialNr());
//				boolean contains = false;
//				for (int i = 0; i < enoughUnwindGoals.size(); i++) {
//					if (enoughUnwindGoals.contains(goal.node().serialNr())) {
//						System.out.println("dieser Goal" + enoughUnwindGoals.get(i) +"ist bereits in der Liste!!!!");
//						contains = true;
//					}
//				}
//				if(enoughUnwindGoals.isEmpty() || !contains){
//					
//					//System.out.println("Found unwind rule!!"); //TODO remove
//					//int unwindRules = computeUnwindRules(goal);
//					//System.out.println(unwindRules); //TODO remove
//					//System.out.println("The limit is "+limitPerLoop);//TODO REMOVE
//
//					
//					if (loops == 0) {
//						if(loopCounter >= 0) {
//							loops = limitPerLoop;//edit for multiple loops, at the moment it works for two loops.
//							loopCounter = loopCounter - 1;
//						}
//						enoughUnwindGoals.add(goal.node().serialNr());
//						return false;
//					} else {
//						loops = loops - 1;
//						GesamtLoopUNwindings = GesamtLoopUNwindings + 1;
//						return true;
//					}
//				}
//				else {
//					System.out.println("FALSE");
//					return false;
//				}
//			}
//			else {
//				return super.isApprovedApp(app, pio, goal);
//				
//			}
//			
//			
//		}

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
