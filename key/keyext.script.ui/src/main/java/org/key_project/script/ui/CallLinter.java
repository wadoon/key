package org.key_project.script.ui;

import edu.kit.iti.formal.psdbg.interpreter.funchdl.DefaultLookup;
import edu.kit.iti.formal.psdbg.lint.Issue;
import edu.kit.iti.formal.psdbg.lint.LintProblem;
import edu.kit.iti.formal.psdbg.lint.LintRule;
import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import lombok.AllArgsConstructor;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (26.07.19)
 */
@AllArgsConstructor
public class CallLinter implements LintRule {
    private final DefaultLookup lookup;

    @Override
    public void check(List<? extends ASTNode> node, List<LintProblem> problems) {
        //TODO check for CallStatement
        //then call handler
        //handle possible exception
        //add LintProblem to problems list
        //Issue.CALL_UNDEFINED
    }

    @Override
    public String getName() {
        return getClass().getSimpleName();
    }
}
