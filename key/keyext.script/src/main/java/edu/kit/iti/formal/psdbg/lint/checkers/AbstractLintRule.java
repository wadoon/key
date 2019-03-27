package edu.kit.iti.formal.psdbg.lint.checkers;

import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import edu.kit.iti.formal.psdbg.lint.*;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (23.05.17)
 */
public abstract class AbstractLintRule implements LintRule {
    private final SearcherFactory factory;

    protected AbstractLintRule(SearcherFactory factory) {
        this.factory = factory;
    }

    @Override
    public void check(List<? extends ASTNode> node, List<LintProblem> problems) {
        Searcher s = factory.create();
        for (ASTNode n : node) {
            n.accept(s);
        }
        problems.addAll(s.getProblems());
    }

    @Override
    public String getName() {
        return getClass().getSimpleName();
    }

}
