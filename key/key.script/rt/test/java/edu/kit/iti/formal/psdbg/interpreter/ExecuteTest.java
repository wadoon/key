package edu.kit.iti.formal.psdbg.interpreter;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.data.State;
import edu.kit.iti.formal.psdbg.parser.ast.Variable;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import org.apache.commons.cli.ParseException;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;

import static edu.kit.iti.formal.psdbg.TestHelper.getFile;

/**
 * @author Alexander Weigl
 * @version 1 (28.05.17)
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
        Assert.assertEquals("Number of goals has to be two ", 2, i.getCurrentGoals().size());
        KeyData goal0_data = currentState.getGoals().get(0).getData();
        Value y = currentState.getGoals().get(0).getAssignments().getValue(new Variable("Y"));
        Assert.assertTrue(goal0_data.getRuleLabel().contains("cut"));
        KeyData goal1_data = currentState.getGoals().get(1).getData();
        Assert.assertTrue(goal1_data.getRuleLabel().contains("cut"));
        DefaultTermParser dp = new DefaultTermParser();

        Term s = dp.parse(new StringReader(y.getData().toString()), Sort.FORMULA, goal0_data.getEnv().getServices(), goal0_data.getProof().getNamespaces(), null);
        Assert.assertEquals("Antecedent should contain the cut formula", s, goal0_data.getNode().sequent().antecedent().get(0).formula());


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

}