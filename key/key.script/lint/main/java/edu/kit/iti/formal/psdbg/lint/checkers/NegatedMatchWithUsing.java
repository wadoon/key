package edu.kit.iti.formal.psdbg.lint.checkers;

import edu.kit.iti.formal.psdbg.lint.Issue;
import edu.kit.iti.formal.psdbg.parser.ast.FunctionCall;
import edu.kit.iti.formal.psdbg.parser.ast.MatchExpression;
import edu.kit.iti.formal.psdbg.parser.ast.UnaryExpression;

/**
 * @author Alexander Weigl
 * @version 1 (23.05.17)
 */
public class NegatedMatchWithUsing extends AbstractLintRule {
    private static Issue ISSUE = Issue.NEGETED_MATCH_WITH_USING;

    public NegatedMatchWithUsing() {
        super(NMWUSearcher::new);
    }

    static class NMWUSearcher extends Searcher {
        @Override
        public Void visit(UnaryExpression ue) {
            if (ue.getExpression() instanceof MatchExpression) {
                MatchExpression me = (MatchExpression) ue.getExpression();
                /*if (me.getSignature() != null && me.getSignature().size() > 0) {
                    problem(ISSUE, ue, me);
                }*/
            }
            return super.visit(ue);
        }

        @Override
        public Void visit(FunctionCall func) {
            return null;
        }
    }
}
