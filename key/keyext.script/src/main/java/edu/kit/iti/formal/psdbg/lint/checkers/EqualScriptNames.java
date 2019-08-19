package edu.kit.iti.formal.psdbg.lint.checkers;

import edu.kit.iti.formal.psdbg.lint.Issue;
import edu.kit.iti.formal.psdbg.lint.LintProblem;
import edu.kit.iti.formal.psdbg.lint.LintRule;
import edu.kit.iti.formal.psdbg.parser.TransformAst;
import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import org.antlr.v4.runtime.Token;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (23.05.17)
 */
public class EqualScriptNames implements LintRule {
    private Issue ISSUE = Issue.EQUAL_SCRIPT_NAMES;
    private Issue ISSUES_MAIN_NAME_USED = Issue.MAIN_NAME_USED;

    @Override
    public void check(List<? extends ASTNode> node, List<LintProblem> problems) {
        Map<String, Token> scripts = new HashMap<>();
        for (ASTNode s : node) {
            if (s instanceof ProofScript) {
                ProofScript proofScript = (ProofScript) s;
                if (scripts.containsKey(proofScript.getName())) {
                    problems.add(LintProblem.create(ISSUE,
                            scripts.get(proofScript.getName()),
                            proofScript.getRuleContext().name));
                }

                if(proofScript.getName().equals(TransformAst.MAIN_SCRIPT_NAME)
                        && proofScript.getRuleContext() != null) {
                    //user defined main script.
                    problems.add(LintProblem.create(ISSUES_MAIN_NAME_USED,
                            proofScript.getRuleContext().name));
                }

                if (proofScript.getRuleContext() != null) {
                    scripts.put(proofScript.getName(),
                            proofScript.getRuleContext().name);
                }
            }
        }
    }

    @Override
    public String getName() {
        return ISSUE.name();
    }
}
