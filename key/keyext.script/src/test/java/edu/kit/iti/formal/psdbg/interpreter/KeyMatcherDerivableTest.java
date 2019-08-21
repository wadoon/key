package edu.kit.iti.formal.psdbg.interpreter;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import static edu.kit.iti.formal.psdbg.TestHelper.getFile;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.matcher.KeYMatcher;
import org.apache.commons.cli.ParseException;
import org.junit.Assert;
import org.junit.Test;

import java.io.File;
import java.io.IOException;

/**
 * Created by weigl on 15.07.2017.
 *
 */
public class KeyMatcherDerivableTest {

    @Test
    public void derivable_test_1() throws Exception {
        //KeYProofFacade f = new KeYProofFacade();
        String file = getClass().getResource("derivable_test_1.key").toExternalForm().substring(5);

        KeYEnvironment<?> env = KeYEnvironment.load(new File(file), null, null, null);

        Proof proof = env.getLoadedProof();

        Goal g = proof.getGoal(proof.root());
        KeyData newKeYData = new KeyData(g, env, proof);
        GoalNode<KeyData> gn = new GoalNode<>(newKeYData);
        Term termQ = new TermBuilder(env.getServices().getTermFactory(),
                env.getServices()).parseTerm("q");
        System.out.println(termQ);
        GoalNode<KeyData> a = KeYMatcher.isDerivable(proof, gn, termQ);
        System.out.println(proof);
        Assert.assertNotNull(a);
        Assert.assertEquals(1, proof.getSubtreeGoals(proof.root()).size());
    }

}