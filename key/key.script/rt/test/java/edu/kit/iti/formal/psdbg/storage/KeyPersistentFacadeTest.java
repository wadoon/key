package edu.kit.iti.formal.psdbg.storage;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofApi;
import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import edu.kit.iti.formal.psdbg.interpreter.InterpreterBuilder;
import edu.kit.iti.formal.psdbg.interpreter.KeyInterpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.data.State;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;
import edu.kit.iti.formal.psdbg.parser.ast.Parameters;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import org.junit.Assert;
import org.junit.Test;

import javax.xml.bind.JAXBException;
import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.ArrayList;

/**
 * @author Alexander Weigl
 * @version 1 (16.05.18)
 */
public class KeyPersistentFacadeTest {
    @Test
    public void testWriteReadXml() throws JAXBException {
        StringWriter writer = new StringWriter();
        PersistentState state = new PersistentState();
        PersistentGoal g1 = new PersistentGoal("g1", false, new ArrayList<>());
        PersistentGoal g2 = new PersistentGoal("g2", true, new ArrayList<>());
        PersistentGoal g3 = new PersistentGoal("g3", false, new ArrayList<>());
        state.getGoals().add(g1);
        state.getGoals().add(g2);
        state.getGoals().add(g3);
        g1.addVariable("a", "INT", "1");
        g2.addVariable("a", "INT", "1");
        g3.addVariable("a", "INT", "1");
        g2.addVariable("b", "BOOL", "FALSE");

        PersistentFacade.write(state, writer);
        String output = writer.getBuffer().toString();
        System.out.println(output);
        PersistentState rstate = PersistentFacade.read(new StringReader(output));

        Assert.assertEquals(state, rstate);
    }


    @Test
    public void testWriteReadKey() throws ProblemLoaderException, IOException, JAXBException {
        File cp = new File("src/test/resources/edu/kit/iti/formal/psdbg/interpreter/contraposition/contraposition.key");
        System.out.println(cp.getAbsolutePath());
        ProofManagementApi a = KeYApi.loadFromKeyFile(cp);
        System.out.println("KeyPersistentFacadeTest.testWriteReadKey");
        ProofApi b = a.getLoadedProof();
        KeYEnvironment env = b.getEnv();
        Proof proof = b.getProof();
        InterpreterBuilder ib = new InterpreterBuilder();
        KeyInterpreter inter = ib.proof(b).startState().scriptCommands().macros().build();
        State<KeyData> state = inter.getCurrentState();

        StringWriter sw = new StringWriter();
        KeyPersistentFacade.write(state, sw);
        System.out.println(sw.toString());
        State<KeyData> rstate = KeyPersistentFacade.read(env, proof, new StringReader(sw.getBuffer().toString()));

        ProofScript ps = new ProofScript();
        CallStatement cs = new CallStatement("impRight", new Parameters());
        ps.getBody().add(cs);
        inter.interpret(ps);

        sw = new StringWriter();
        KeyPersistentFacade.write(state, sw);
        System.out.println(sw.toString());
        State<KeyData> state1 = KeyPersistentFacade.read(env, proof, new StringReader(sw.getBuffer().toString()));

    }
}