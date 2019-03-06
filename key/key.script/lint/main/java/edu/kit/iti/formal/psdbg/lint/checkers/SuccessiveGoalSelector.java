package edu.kit.iti.formal.psdbg.lint.checkers;

import edu.kit.iti.formal.psdbg.lint.Issue;
import edu.kit.iti.formal.psdbg.parser.ast.*;

import java.util.Objects;

/**
 * @author Alexander Weigl
 * @version 1 (23.05.17)
 */
public class SuccessiveGoalSelector extends AbstractLintRule {
    private static Issue SUCC_SAME_BLOCK =
            Issue.SUCC_SAME_BLOCK;
    private static final Issue FOREACH_AFTER_THEONLY =
            Issue.FOREACH_AFTER_THEONLY;
    private static final Issue THEONLY_AFTER_FOREACH =
            Issue.THEONLY_AFTER_FOREACH;

    public SuccessiveGoalSelector() {
        super(SGSearcher::new);
    }

    static class SGSearcher extends Searcher {

        @Override
        public Void visit(TheOnlyStatement theOnly) {
            if (check(theOnly, theOnly.getNodeName())) {
                problem(SUCC_SAME_BLOCK,
                        theOnly, theOnly.getBody().get(0));
            }

            if (check(theOnly, "ForeachStatement")) {
                problem(FOREACH_AFTER_THEONLY, theOnly, theOnly.getBody().get(0));
            }

            return super.visit(theOnly);
        }

        private boolean check(UnconditionalBlock gs, String forbidden) {
            return gs.getBody().size() > 0 && Objects.equals(gs.getBody().get(0).getNodeName(), forbidden);
        }

        @Override
        public Void visit(ForeachStatement foreach) {
            if (check(foreach, foreach.getNodeName())) {
                problem(SUCC_SAME_BLOCK,
                        foreach, foreach.getBody().get(0));
            }

            if (check(foreach, "TheOnlyStatement")) {
                problem(THEONLY_AFTER_FOREACH,
                        foreach, foreach.getBody().get(0));
            }
            return super.visit(foreach);
        }

        @Override
        public Void visit(RepeatStatement repeat) {
            if (check(repeat, repeat.getNodeName())) {
                problem(SUCC_SAME_BLOCK,
                        repeat, repeat.getBody().get(0));
            }
            return super.visit(repeat);
        }

        @Override
        public Void visit(FunctionCall func) {
            return null;
        }
    }
}