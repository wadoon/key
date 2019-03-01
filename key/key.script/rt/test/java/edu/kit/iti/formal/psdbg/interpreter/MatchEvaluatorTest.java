package edu.kit.iti.formal.psdbg.interpreter;

import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.interpreter.dbg.PseudoMatcher;
import edu.kit.iti.formal.psdbg.parser.ast.Variable;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import org.junit.Before;

/**
 * Created by sarah on 5/23/17.
 */

public class MatchEvaluatorTest {
    MatchEvaluator mEval;

    @Before
    public void setup() {
        GoalNode<String> parent = new GoalNode<>("pa");
        parent.declareVariable(new Variable("a"), SimpleType.INT);
        parent.declareVariable(new Variable("b"), SimpleType.INT);
        VariableAssignment va = parent.getAssignments();
        va.assign(new Variable("a"), Value.from(1));
        va.assign(new Variable("b"), Value.from(1));
        GoalNode<String> selected = new GoalNode<>(parent, "selg", false);
        mEval = new MatchEvaluator(va, selected, new PseudoMatcher());
    }

}
