package org.key_project.script.ui;

import edu.kit.iti.formal.psdbg.interpreter.exceptions.NoCallHandlerException;
import edu.kit.iti.formal.psdbg.interpreter.funchdl.DefaultLookup;
import edu.kit.iti.formal.psdbg.lint.Issue;
import edu.kit.iti.formal.psdbg.lint.LintProblem;
import edu.kit.iti.formal.psdbg.lint.checkers.AbstractLintRule;
import edu.kit.iti.formal.psdbg.lint.checkers.Searcher;
import edu.kit.iti.formal.psdbg.lint.checkers.SearcherFactory;
import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import edu.kit.iti.formal.psdbg.parser.ast.Statements;
import lombok.AllArgsConstructor;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl, S.Grebing
 * @version 1 (26.07.19)
 */
public class CallLinter extends AbstractLintRule {
    @Override
    public void check(List<? extends ASTNode> node, List<LintProblem> problems) {
        super.check(node, problems);

    }

    private final DefaultLookup lookup;

    protected CallLinter(DefaultLookup lookup) {
        super(new CallLintSearcher(lookup));
        this.lookup = lookup;

    }

//    @Override
/*    public void check(List<? extends ASTNode> node, List<LintProblem> problems) {
        node.forEach(o -> {
        if(o instanceof ProofScript){
            ProofScript ps = (ProofScript) o;
            Statements body = ps.getBody();
            body.forEach(statement -> {
                if(statement instanceof CallStatement) {
                    try {
                        lookup.getBuilder((CallStatement) statement, null);
                    } catch (NoCallHandlerException nce) {
                        Issue callUndefined = Issue.CALL_UNDEFINED;

                        LintProblem lp = new LintProblem(callUndefined);
                        List<Token> tokens = new ArrayList<Token>();
                        tokens.add(statement.getRuleContext().getStart());
                        tokens.add(statement.getRuleContext().getStop());
                        lp.setMarkTokens(tokens);
                        problems.add(lp);
                    }
                }
            });
        }
        });
    }*/

    public String getName() {
        return getClass().getSimpleName();
    }

    private static class CallLintSearcher implements SearcherFactory {
        DefaultLookup lookup;
        public CallLintSearcher(DefaultLookup lookup) {
            this.lookup = lookup;
        }

        @Override
        public Searcher create() {
            return new CallLintVisitor(lookup);
        }

        private class CallLintVisitor extends Searcher {
            DefaultLookup lookup;
            public CallLintVisitor(DefaultLookup lookup) {
                super();
                this.lookup = lookup;
            }

            @Override
            public Void visit(ProofScript proofScript) {
                return super.visit(proofScript);
            }

            @Override
            public Void visit(Statements statements) {
                return super.visit(statements);
            }

            @Override
            public Void visit(CallStatement call) {

                try {
                    lookup.getBuilder(call, null);
                } catch (NoCallHandlerException nce) {
                    Issue callUndefined = Issue.CALL_UNDEFINED;

                    LintProblem lp = new LintProblem(callUndefined);
                    List<Token> tokens = new ArrayList<Token>();
                    tokens.add(call.getRuleContext().getStart());
                    tokens.add(call.getRuleContext().getStop());
                    lp.setMarkTokens(tokens);
                    problems.add(lp);
                }
                return super.visit(call);
            }

        }
    }
}
