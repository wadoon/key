package edu.kit.iti.formal.psdbg.lint.checkers;

import edu.kit.iti.formal.psdbg.parser.ASTTraversal;
import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import edu.kit.iti.formal.psdbg.lint.Issue;
import edu.kit.iti.formal.psdbg.lint.LintProblem;
import lombok.Getter;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (23.05.17)
 */
public abstract class Searcher implements ASTTraversal<Void> {
    @Getter
    protected final List<LintProblem> problems = new ArrayList<>(10);

    LintProblem problem(Issue issue) {
        LintProblem lp = new LintProblem(issue);
        problems.add(lp);
        return lp;
    }

    LintProblem problem(Issue issue, ASTNode... nodes) {
        return problem(issue).nodes(nodes);
    }
}
