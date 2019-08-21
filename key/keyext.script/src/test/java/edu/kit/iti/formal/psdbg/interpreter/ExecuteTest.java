package edu.kit.iti.formal.psdbg.interpreter;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.data.State;
import edu.kit.iti.formal.psdbg.interpreter.data.TermValue;
import edu.kit.iti.formal.psdbg.parser.ast.Variable;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import org.apache.commons.cli.ParseException;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.util.List;

import static edu.kit.iti.formal.psdbg.TestHelper.getFile;

/**
 * This class test the KeYInterpreter by using the command line implementation
 * @author Alexander Weigl
 * @version 1 (28.05.17)
 * @version 2 by S.Grebing August 2019
 */
public class ExecuteTest {
    private static Execute create(String... cmd) throws IOException, ParseException {
        Execute e = new Execute();
        e.init(cmd);
        return e;
    }

    @Test
    public void testContrapositionAuto() throws IOException, ParseException {
        Execute execute = create(
                getFile(getClass(), "contraposition/contraposition.key"),
                "-s", getFile(getClass(), "contraposition/auto.kps"));
        Interpreter<KeyData> i = execute.run();
        System.out.println(i.getCurrentState());
    }

    @Test
    public void testContrapositionManualWoBranching() throws IOException, ParseException {
        Execute execute = create(
                getFile(getClass(), "contraposition/contraposition.key"),
                "-s", getFile(getClass(), "contraposition/wo_branching.kps"));
        execute.run();
    }

    @Test
    public void testContrapositionManualWBranching() throws IOException, ParseException {
        Execute execute = create(
                getFile(getClass(), "contraposition/contraposition.key"),
                "-s", getFile(getClass(), "contraposition/w_branching.kps"));
        Interpreter<KeyData> i = execute.run();
        System.out.println(i.getCurrentState());

    }

    @Test
    public void testContrapositionCut() throws IOException, ParseException, ParserException {
        Execute execute = create(
                getFile(getClass(), "contraposition/contraposition.key"),
                "-s", getFile(getClass(), "contraposition/cutTest.kps"));
        Interpreter<KeyData> i = execute.run();
        State<KeyData> currentState = i.getCurrentState();
        System.out.println(currentState);
        //This revealed a bug in the interpreter for body of a case
        Assert.assertEquals("Number of goals has to be two ", 4, i.getCurrentGoals().size());
        KeyData goal0_data = currentState.getGoals().get(0).getData();
        Value y = currentState.getGoals().get(0).getAssignments().getValue(new Variable("Y"));
        Assert.assertTrue(goal0_data.getRuleLabel().contains("cut"));
        KeyData goal1_data = currentState.getGoals().get(1).getData();
        Assert.assertTrue(goal1_data.getRuleLabel().contains("cut"));
        DefaultTermParser dp = new DefaultTermParser();

        Term s = dp.parse(new StringReader(y.getData().toString()), Sort.FORMULA,
                goal0_data.getProof().getServices(),
                goal0_data.getProof().getNamespaces(), null);

        Assert.assertEquals("Antecedent should contain the cut formula", s,
                goal0_data.getNode().sequent().antecedent().get(0).formula());


    }

    @Test
    public void testLiarsville() throws IOException, ParseException, ParserException {
        Execute execute = create(
                getFile(getClass(), "testCasesKeYFiles/liarsville.key"),
                "-s", getFile(getClass(), "testCasesKeYFiles/liarsvilleAuto.kps"));
        Interpreter<KeyData> i = execute.run();
        State<KeyData> currentState = i.getCurrentState();
        System.out.println(currentState);
        //This revealed a bug in the interpreter for body of a case


    }

    @Test
    public void testInstantiate() throws IOException, ParseException, ParserException {
        File proof = new File("/home/sarah/Documents/KIT_Mitarbeiter/ProofScriptingLanguage/bigIntProof/compareMagnitude_openCases.key.proof");
        File script = new File("/home/sarah/Documents/KIT_Mitarbeiter/ProofScriptingLanguage/bigIntProof/instAll.kps");
        Assume.assumeTrue(proof.exists()); //
        Execute exec = create(proof.getAbsolutePath(), "-s", script.getAbsolutePath());
        Interpreter<KeyData> i = exec.run();
        State<KeyData> currentState = i.getCurrentState();
        System.out.println(currentState);
    }


    /**
     * This test reveiled an already fixed bug in the KeYevluator for Subtitution expressions
     * @throws IOException
     * @throws ParseException
     * @throws ParserException
     */
    @Test
    public void testSubstitutionOfMatch() throws IOException, ParseException, ParserException {
        Execute execute = create(
                getFile(getClass(), "contraposition/contraposition.key"),
                "-s", getFile(getClass(), "contraposition/subst.kps"));
        Interpreter<KeyData> i = execute.run();
        State<KeyData> currentState = i.getCurrentState();

        KeyData goal0_data = currentState.getGoals().get(0).getData();
        Value f = currentState.getGoals().get(0).getAssignments().getValue(new Variable("F")); //should be !p->!q

        Value x = currentState.getGoals().get(0).getAssignments().getValue(new Variable("X")); //should be !p->!q

        Value y = currentState.getGoals().get(0).getAssignments().getValue(new Variable("Y")); //should be p->q
        Value z = currentState.getGoals().get(0).getAssignments().getValue(new Variable("Z"));

        Assert.assertEquals("The substituted variable values must be identical", x.getData(), ((TermValue) f.getData()).getTermRepr());
        Assert.assertEquals("The substituted variable values must be identical", y.getData(), ((TermValue) z.getData()).getTermRepr());
     }

    /***
     * This test should test that if a try block is used and teh content does not close the proof it is rolled back
     * @throws IOException
     * @throws ParseException
     * @throws ProblemLoaderException
     */
    @Test
    public void testTryFail() throws IOException, ParseException {
        Execute execute = create(getFile(getClass(), "contraposition/contraposition.key"), "-s",
                getFile(getClass(), "contraposition/testIsClosable.kps"));
        Interpreter<KeyData> i = execute.run();

        List<GoalNode<KeyData>> goals = i.getCurrentState().getGoals();
        Assert.assertEquals(2, goals.size());
        for (GoalNode<KeyData> goal : goals) {
            Assert.assertEquals("Label for node " + goal.getData().getNode(), "impLeft // impRight // $$", goal.getData().getRuleLabel());
        }

    }

    /**
     * This test test that the closes statement as match expression for a case branch is effectless if the content does not close th proof
     * @throws IOException
     * @throws ParseException
     */
    @Test
    public void testClosesFail() throws IOException, ParseException {
        Execute execute = create(getFile(getClass(), "contraposition/contraposition.key"), "-s",
                getFile(getClass(), "contraposition/closes.kps"));
        Interpreter<KeyData> i = execute.run();

        List<GoalNode<KeyData>> goals = i.getCurrentState().getGoals();
        Assert.assertEquals(2, goals.size());
        for (GoalNode<KeyData> goal : goals) {
            Assert.assertEquals("Label for node " + goal.getData().getNode(), "impLeft // impRight // $$", goal.getData().getRuleLabel());
        }

        // Assert.assertEquals(10, i.getCurrentState().getGoals().size());
    }


    /**
     * This test tests a successful closes block taht is rolled back and because it would close the proof the
     * case branch is executed, which should not close the proof. If teh proof is closed the case branch was skipped
     * and teh default branch was exectued instead.
     * @throws IOException
     * @throws ParseException
     */
    @Test
    public void testClosesScriptSuccess() throws IOException, ParseException {
        Execute execute = create(getFile(getClass(), "contraposition/contraposition.key"), "-s",
                getFile(getClass(), "contraposition/closesSuccess.kps"));
        Interpreter<KeyData> i = execute.run();
        List<GoalNode<KeyData>> goals = i.getCurrentState().getGoals();
        Assert.assertEquals(2, goals.size());
        for (GoalNode<KeyData> goal : goals) {
            Assert.assertEquals("Label for node " + goal.getData().getNode(), "impRight // impLeft // impRight // $$", goal.getData().getRuleLabel());
        }

        Assert.assertFalse("The proof is not closed goal 0", goals.get(0).isClosed());
        Assert.assertFalse("The proof is not closed goal 1", goals.get(1).isClosed());


    }

    /**
     * This test test that the extra variables are correctly used
     * @throws IOException
     * @throws ParseException
     */
    @Test
    public void testHookAssignments() throws IOException, ParseException {
        Execute execute = create(getFile(getClass(), "contraposition/contraposition.key"), "-s",
                getFile(getClass(), "contraposition/hookTestScript.kps"));
        Interpreter<KeyData> i = execute.run();


        Assert.assertTrue(i.isStrictMode());

    }
}