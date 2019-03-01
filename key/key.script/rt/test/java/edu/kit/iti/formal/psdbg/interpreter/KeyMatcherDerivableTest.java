package edu.kit.iti.formal.psdbg.interpreter;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.matcher.KeYMatcher;
import org.junit.Assert;
import org.junit.Test;

import java.io.File;

/**
 * Created by weigl on 15.07.2017.
 */
public class KeyMatcherDerivableTest {
    @Test
    public void derivable_test_1() throws Exception {
        KeYProofFacade f = new KeYProofFacade();
        String file = getClass().getResource("derivable_test_1.key").toExternalForm().substring(5);
        f.loadKeyFileSync(new File(file));
        Proof proof = f.getProof();

        Goal g = proof.getGoal(proof.root());
        KeyData newKeYData = new KeyData(g, f.getEnvironment(), proof);
        GoalNode<KeyData> gn = new GoalNode<>(newKeYData);
        Term termQ = new TermBuilder(f.getEnvironment().getServices().getTermFactory(),
                f.getEnvironment().getServices()).parseTerm("q");
        System.out.println(termQ);
        GoalNode<KeyData> a = KeYMatcher.isDerivable(proof, gn, termQ);


        System.out.println(proof);

        Assert.assertNotNull(a);

        Assert.assertEquals(1, proof.getSubtreeGoals(proof.root()).size());
    }

}