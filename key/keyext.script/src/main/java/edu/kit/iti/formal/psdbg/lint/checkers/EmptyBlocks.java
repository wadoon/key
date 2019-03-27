package edu.kit.iti.formal.psdbg.lint.checkers;

import edu.kit.iti.formal.psdbg.lint.Issue;
import edu.kit.iti.formal.psdbg.parser.ast.*;

/**
 * @author Alexander Weigl
 * @version 1 (23.05.17)
 */
public class EmptyBlocks extends AbstractLintRule {
    private static Issue EMPTY_BLOCK = Issue.EMPTY_BLOCKS;

    public EmptyBlocks() {
        super(EmptyBlockSearcher::new);
    }

    private static class EmptyBlockSearcher extends Searcher {

        @Override
        public Void visit(FunctionCall func) {
            return null;
        }

        public void check(ASTNode node, Statements statements) {
            if (statements.size() == 0) {
                problem(EMPTY_BLOCK, node);
            }
        }

        @Override
        public Void visit(ProofScript proofScript) {
            check(proofScript, proofScript.getBody());
            return super.visit(proofScript);
        }

        @Override
        public Void visit(CaseStatement caseStatement) {
            check(caseStatement, caseStatement.getBody());
            return super.visit(caseStatement);
        }

        @Override
        public Void visit(TheOnlyStatement theOnly) {
            check(theOnly, theOnly.getBody());
            return super.visit(theOnly);
        }

        @Override
        public Void visit(ForeachStatement foreach) {
            check(foreach, foreach.getBody());
            return super.visit(foreach);
        }

        @Override
        public Void visit(RepeatStatement repeatStatement) {
            check(repeatStatement, repeatStatement.getBody());
            return super.visit(repeatStatement);
        }
    }
}
