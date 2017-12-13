package de.uka.ilkd.key.macros;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;


import de.uka.ilkd.key.logic.JavaBlock;
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
		private static HashMap<Integer, JavaBlock> nodeJavaBlockMap;
		
		static {
			nodeJavaBlockMap = new HashMap<Integer, JavaBlock>();
		}
		
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
		
//		/**
//		 * check if the applied rule of the node is a "ifsplit" rule
//		 * @param node the node you want to check
//		 * @return true if the applied rule is "ifSplit"
//		 */
//		private boolean isIfSplitRule(Node node) {
//			if (node.getAppliedRuleApp().rule().name().toString().equals(IFSPLIT)) {
//				return true;
//			}
//			return false;
//		}
		
		private int computeUnwindRules(Goal goal, PosInOccurrence pio) {
			JavaBlock currentBlock = pio.subTerm().javaBlock();
			Node currentNode = goal.node();
			int unwindings = 0;
			//remember every javaBlock with unwind rule node
			
			nodeJavaBlockMap.put(currentNode.serialNr(), currentBlock);
			
			//now count number of unwind rules with same java block 
			//(use the hasmap to get the corresponding javablock)
			while(!currentNode.root()) {
				RuleApp app = currentNode.getAppliedRuleApp();
				if (app != null) {
					if(isUnwindRule(app.rule())) {
						JavaBlock javaBlockCurrentNode = nodeJavaBlockMap.get(currentNode.serialNr());
						if(currentBlock.equals(javaBlockCurrentNode)) {
							++unwindings;
						}
						
					}
				}
				currentNode = currentNode.parent();
			}
			return unwindings;
			
		}
		
		
//		private int computeUnwindRulesJavaBlockSignature(Goal goal, PosInOccurrence pio) {
//			int unwinds = 0;
//			JavaBlock currentBlock = pio.subTerm().javaBlock();
//			boolean found = false;
//			System.out.println("current javablock programm ::: " + currentBlock.toString());
//			System.out.println("TEST ..... ::: "+ currentBlock.program().getFirstElementIncludingBlocks());
//			
//			
//			for (int i = 0; i < loopJavaBlocks.size(); i++){
//				if (loopJavaBlocks.get(i).first.equals(currentBlock)) {
//					System.out.println("verglichen mit Block :: " + loopJavaBlocks.get(i).toString());
//					System.out.println("Ja");
//					System.out.println("anzahl unwinds:: " + loopJavaBlocks.get(i).second);
//					Pair<JavaBlock, Integer> currentPair = loopJavaBlocks.get(i);
//					unwinds = loopJavaBlocks.get(i).second + 1;
//					currentPair = new Pair<JavaBlock, Integer>(currentBlock, unwinds);
//					loopJavaBlocks.set(i, currentPair);
//					found = true;
//				}
//			}
//			if (!found) {
//				loopJavaBlocks.add(new Pair<JavaBlock, Integer>(currentBlock, 0));
//				unwinds = 0;
//				System.out.println("hinzufügen");
//			}
//			
//			return unwinds;
			
//			Node currentNode = goal.node();
//			int totalUnwinds = 0;
//			while (!currentNode.root()) {
//				final RuleApp app = currentNode.getAppliedRuleApp();
//				if (app != null) {
//					final Rule rule = app.rule();
//					if (TestGenInfoFlowStrategy.isUnwindRule(rule)) {
//						
//						++totalUnwinds;
//					}
//				}
//				currentNode = currentNode.parent();
//			}
//			
//			
//			
//			//return totalUnwinds;
//			
//			//TODO Save loop signature and count for each loop and traverse the tree like TestGenMacro
//			//String[] loopSignatur = currentNode.name().split("\\{");
//			
//			//System.out.println("node name :: "+loopSignatur[0]);
//			for (int i = 0; i < loopSignatures.size(); i++) {
//				//loop already in list
//				if (loopSignatures.get(i).first.equals(currentNode.name())) {
//					int unwinds = loopSignatures.get(i).second;
//					Pair<String, Integer> currentPair = loopSignatures.get(i);
//					currentPair = new Pair<String, Integer>(currentNode.name(), unwinds+1);
//					loopSignatures.set(i, currentPair);
//					unwinds = unwinds +1;
//					return unwinds;
//				}
//			}
//			
//			//new Loop
//			loopSignatures.add(new Pair<String, Integer>(currentNode.name(), 1));
//			return 1;
			
//		}
		
//		/**
//		 * this method count the number of unwind rules for the current loop. 
//		 * @param goal the current goal
//		 * @return the number of unwind rules used for the current loop
//		 */
//		private int computeUnwindRules(Goal goal) {
//			int unwindings = 0;
//			Node prevNode = goal.node();
//			Node currentNode = goal.node();
//			while(!currentNode.root()) {
//				final RuleApp app = currentNode.getAppliedRuleApp();
//				if (app != null) {
//					if (isUnwindRule(app.rule())) {
//						//count unwindings used for this loop
//						++unwindings;
//					}
//				}
//				prevNode = currentNode;
//				currentNode = currentNode.parent();
//				
//				if (!currentNode.root()) {
//					//check if the applied rule is if split and belongs to an unwind rule
//					if (isIfSplitRule(currentNode)) {
//						
//						belongsToUnwind = false;
//						
//						//check if the current ifSplit rule belongs to an unwinding rule 
//						Node checkNode = currentNode.parent();
//						while(!checkNode.root()) {
//							RuleApp appIfSplit = checkNode.getAppliedRuleApp();
//							if(isIfSplitRule(checkNode)) {
//								break;
//								//last if split does not belong to unwind rule
//							}
//							if(isUnwindRule(appIfSplit.rule())) {
//								//the current ifSplitNode belongs to the unwinding rule
//								belongsToUnwind = true;
//								break;
//							}
//							checkNode = checkNode.parent();
//						}
//						
//						if(belongsToUnwind) {
//							// if left child node, stop count (unwinding rules above are part of other loops)
//							if(currentNode.child(1).equals(prevNode)) {
//								break;
//							}
//						}
//						
//					}
//				}
//			}
//			return unwindings;
//			
//		}
		
		@Override
		public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
			
			if (!TestGenInfoFlowMacro.hasModality(goal.node())) {
				return false;
			}
			
			if (TestGenInfoFlowStrategy.isUnwindRule(app.rule())) {
//				System.out.println(pio.subTerm().javaBlock().toString());
				
//				System.out.println(pio.down(0).subTerm().javaBlock().toString());
				
				
				int unwindings = computeUnwindRules(goal, pio);
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
