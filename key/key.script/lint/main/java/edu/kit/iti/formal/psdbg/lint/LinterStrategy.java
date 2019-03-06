package edu.kit.iti.formal.psdbg.lint;

import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import lombok.Getter;

import java.util.ArrayList;
import java.util.List;
import java.util.ServiceLoader;

/**
 * @author Alexander Weigl
 * @version 1 (23.05.17)
 */
public class LinterStrategy {
    @Getter
    private List<LintRule> checkers = new ArrayList<>();

    public List<LintProblem> check(List<ProofScript> nodes) {
        List<LintProblem> problems = new ArrayList<>(1024);
        for (LintRule checker : checkers) {
            checker.check(nodes, problems);
        }
        return problems;
    }

    public static LinterStrategy getDefaultLinter() {
        LinterStrategy ls = new LinterStrategy();
        ServiceLoader<LintRule> loader = ServiceLoader.load(LintRule.class);
        loader.forEach(ls.checkers::add);
        return ls;
    }
}
