package org.key_project.script.ui;

import edu.kit.iti.formal.psdbg.interpreter.exceptions.NoCallHandlerException;
import edu.kit.iti.formal.psdbg.interpreter.funchdl.DefaultLookup;
import edu.kit.iti.formal.psdbg.lint.Issue;
import edu.kit.iti.formal.psdbg.lint.LintProblem;
import edu.kit.iti.formal.psdbg.lint.LintRule;
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
@AllArgsConstructor
public class CallLinter implements LintRule {
    private final DefaultLookup lookup;

    @Override
    public void check(List<? extends ASTNode> node, List<LintProblem> problems) {
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
    }

    @Override
    public String getName() {
        return getClass().getSimpleName();
    }
}
