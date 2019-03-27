package edu.kit.iti.formal.psdbg.interpreter;

import edu.kit.iti.formal.psdbg.TestHelper;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.dbg.PseudoMatcher;
import edu.kit.iti.formal.psdbg.parser.ast.Expression;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;

/**
 * @author Alexander Weigl
 * @version 1 (16.05.17)
 */
@RunWith(Parameterized.class)
public class EvaluatorTest {
    private final Expression expr, truth;
    private Evaluator eval;

    public EvaluatorTest(String e, String r) {
        expr = TestHelper.toExpr(e);
        truth = TestHelper.toExpr(r);
    }

    @Parameterized.Parameters(name = "{0} => {1}")
    public static Iterable<Object[]> expr() throws IOException {
        return TestHelper.loadLines("eval.txt", 2);
    }

    @Before
    public void setup() {
        GoalNode<String> parent = new GoalNode<>( "pa");
        parent.getAssignments()
                .declare("a", SimpleType.INT)
                .declare("b", SimpleType.INT)
                .assign("a", Value.from(1))
                .assign("b", Value.from(1));
        GoalNode<String> selected = new GoalNode<>(parent, "selg", false);
        eval = new Evaluator<>(selected.getAssignments(), selected);
        eval.setMatcher(new PseudoMatcher());
    }

    @Test
    public void testEval() {
        Value result = eval.eval(expr);
        Value truthValue = eval.eval(truth);
        System.out.println(expr);
        Assert.assertEquals(truthValue, result);
    }
}