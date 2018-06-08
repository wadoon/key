package de.uka.ilkd.key.macros;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.SourceElement;
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
 * Macro for test generation which perform double symbolic execution for noninterference-proofs
 * (include loop unwinding for multiple loops)
 * @author Muessig
 *
 */
public class TestGenInfoFlowMacro extends StrategyProofMacro {

    private static class TestGenInfoFlowStrategy extends FilterStrategy {

        /**
         * name of the macro
         */
        private static final Name NAME = new Name(TestGenInfoFlowStrategy.class.getSimpleName());
        /**
         * set of rules needed for the macro
         */
        private static final Set<String> UNWIND_RULES;
        /**
         * costs for an unwind rule
         */
        private static final int UNWIND_COST = 1000;
        /**
         * hash map with node serialNr and the loop unwound at this node.
         * Use this to check how often the current loop is unwound
         */
        private static HashMap<Integer, SourceElement> nodeJavaBlockMap;
        /**
         * unwind limit per loop
         */
        private final int limitPerLoop;

        static {
            nodeJavaBlockMap = new HashMap<Integer, SourceElement>();
        }

        static {
            UNWIND_RULES = new HashSet<String>();
            TestGenInfoFlowStrategy.UNWIND_RULES.add("loopUnwind");
            TestGenInfoFlowStrategy.UNWIND_RULES.add("doWhileUnwind");
            TestGenInfoFlowStrategy.UNWIND_RULES.add("methodCall");
            TestGenInfoFlowStrategy.UNWIND_RULES.add("methodCallWithAssignment");
            TestGenInfoFlowStrategy.UNWIND_RULES.add("staticMethodCall");
            TestGenInfoFlowStrategy.UNWIND_RULES.add("staticMethodCallWithAssignment");
        }

        public TestGenInfoFlowStrategy(Strategy delegate) {
            super(delegate);
            limitPerLoop = ProofIndependentSettings.DEFAULT_INSTANCE.
                    getTestGenerationSettings().getMaximalUnwinds();
        }

        private static boolean isUnwindRule(Rule rule) {
            if (rule == null) {
                return false;
            }
            final String name = rule.name().toString();
            return TestGenInfoFlowStrategy.UNWIND_RULES.contains(name);
        }

        @Override
        public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {
            if (TestGenInfoFlowStrategy.isUnwindRule(app.rule())) {
                return NumberRuleAppCost.create(TestGenInfoFlowStrategy.UNWIND_COST);
            }
            return super.computeCost(app, pio, goal);
        }

        private int computeUnwindRules(Goal goal, PosInOccurrence pio, RuleApp appGoal) {
            JavaBlock currentBlock = null;

            // search for the programm element
            if (pio.subTerm().javaBlock().isEmpty()) {
                for (Term t : pio.subTerm().subs()) {
                    if (!t.javaBlock().isEmpty()) {
                        currentBlock = t.javaBlock();
                        break;
                    }
                }
            } else {
                currentBlock = pio.subTerm().javaBlock();
            }
            if (currentBlock == null) {
                System.out.println("Warning: java block not found");
                currentBlock = pio.subTerm().javaBlock();
            }

            Node currentNode = goal.node();
            int unwindings = 0;
            SourceElement element = currentBlock.program().getFirstElementIncludingBlocks();
            if (appGoal.rule().name().toString().equals("loopUnwind")
                    || appGoal.rule().name().toString().equals("doWhileUnwind")) {
                String whileString = element.toString();
                // filter the javaBlock (get the loop)
                while (!whileString.startsWith("while")) {
                    element = element.getFirstElementIncludingBlocks();
                    whileString = element.toString();
                }
            }

            // TODO maybe add the same thing for doWhileLoops ?

            // remember every javaBlock with unwind rule node
            nodeJavaBlockMap.put(currentNode.serialNr(), element);

            // now count number of unwind rules with same java block
            while (!currentNode.root()) {
                RuleApp app = currentNode.getAppliedRuleApp();
                if (app != null) {
                    if (isUnwindRule(app.rule())) {
                        SourceElement currentElement = nodeJavaBlockMap.get(currentNode.serialNr());
                        if (element.equals(currentElement)) {
                            ++unwindings;
                        }
                    }
                }
                currentNode = currentNode.parent();
            }
            return unwindings;

        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {

            if (!TestGenInfoFlowMacro.hasModality(goal.node())) {
                return false;
            }

            if (TestGenInfoFlowStrategy.isUnwindRule(app.rule())) {
                if (limitPerLoop == 0) {
                    return false;
                }
                int unwindings = computeUnwindRules(goal, pio, app);
                return !(unwindings >= limitPerLoop);
            }
            return super.isApprovedApp(app, pio, goal);


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
        return new TestGenInfoFlowStrategy(proof.getActiveStrategy());
    }

}
