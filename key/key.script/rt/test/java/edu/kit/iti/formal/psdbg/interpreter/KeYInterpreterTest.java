package edu.kit.iti.formal.psdbg.interpreter;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.parser.Facade;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.List;

/**
 * Created by sarah on 8/2/17.
 */
public class KeYInterpreterTest {
    KeYProofFacade facade;

    @Before
    public void init() {
        facade = new KeYProofFacade();
    }

    public Interpreter<KeyData> execute(InputStream is) throws IOException {
        List<ProofScript> scripts = Facade.getAST(CharStreams.fromStream(is));
        InterpreterBuilder ib = facade.buildInterpreter();
        Interpreter<KeyData> i = ib.build();
        i.interpret(scripts.get(0));
        return i;
    }


    @Test
    public void testTryFail() throws IOException, ProblemLoaderException {
        facade.loadKeyFileSync(new File("src/test/resources/edu/kit/iti/formal/psdbg/interpreter/contraposition/contraposition.key"));
        Interpreter<KeyData> i = execute(getClass().getResourceAsStream("contraposition/testIsClosable.kps"));
        List<GoalNode<KeyData>> goals = i.getCurrentState().getGoals();
        Assert.assertEquals(2, goals.size());
        for (GoalNode<KeyData> goal : goals) {
            Assert.assertEquals("Label for node " + goal.getData().getNode(), "impLeft // impRight // $$", goal.getData().getRuleLabel());
        }

    }

    @Test
    public void testClosesFail() throws IOException, ProblemLoaderException {
        facade.loadKeyFileSync(new File("src/test/resources/edu/kit/iti/formal/psdbg/interpreter/contraposition/contraposition.key"));
        Interpreter<KeyData> i = execute(getClass().getResourceAsStream("contraposition/closes.kps"));
        List<GoalNode<KeyData>> goals = i.getCurrentState().getGoals();
        Assert.assertEquals(2, goals.size());
        for (GoalNode<KeyData> goal : goals) {
            Assert.assertEquals("Label for node " + goal.getData().getNode(), "impLeft // impRight // $$", goal.getData().getRuleLabel());
        }

        // Assert.assertEquals(10, i.getCurrentState().getGoals().size());
    }

    @Test
    public void testClosesScriptSuccess() throws IOException, ProblemLoaderException {
        facade.loadKeyFileSync(new File("src/test/resources/edu/kit/iti/formal/psdbg/interpreter/contraposition/contraposition.key"));
        Interpreter<KeyData> i = execute(getClass().getResourceAsStream("contraposition/closesSuccess.kps"));
        List<GoalNode<KeyData>> goals = i.getCurrentState().getGoals();
        Assert.assertEquals(2, goals.size());
        for (GoalNode<KeyData> goal : goals) {
            Assert.assertEquals("Label for node " + goal.getData().getNode(), "impRight // impLeft // impRight // $$", goal.getData().getRuleLabel());
        }


    }

    @Test
    public void testHookAssignments() throws IOException, ProblemLoaderException {
        facade.loadKeyFileSync(new File("src/test/resources/edu/kit/iti/formal/psdbg/interpreter/contraposition/contraposition.key"));
        Interpreter<KeyData> i = execute(getClass().getResourceAsStream("contraposition/hookTestScript.kps"));
        Assert.assertTrue(i.isStrictMode());

    }


}
