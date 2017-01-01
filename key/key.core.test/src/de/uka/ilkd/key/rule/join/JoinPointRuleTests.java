package de.uka.ilkd.key.rule.join;

import java.io.File;

import org.junit.Test;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.JoinPointStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.BlockContractBuiltInRuleApp;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;
import junit.framework.TestCase;

public class JoinPointRuleTests extends TestCase {

    private static final String TEST_RESOURCES_DIR_PREFIX = "resources/testcase/joinPoint/";

    public JoinPointRuleTests() {
        // TODO Auto-generated constructor stub
    }

    @Test
    public void testJoinPointStatement() {
        final Proof proof = loadProof("AbsBlockContract.ITE.proof");
        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }

    @Test
    public void testNestedJoinBlockContract1() {
        final Proof proof = loadProof("AbsBlockContract.nested.1.proof");
        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }

    @Test
    public void testNestedJoinBlockContract2() {
        final Proof proof = loadProof("AbsBlockContract.nested.2.proof");
        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }

    @Test
    public void testAddJPS() {
        final Proof proof = loadProof(
                "absBlockContract.addJoinPointStatement.key");

        Node nodeBefore = proof.openGoals().head().node();

        startAutomaticStrategy(proof);

        assertTrue(proof.openGoals().head().appliedRuleApps()
                .head() instanceof BlockContractBuiltInRuleApp);

        Node nodeAfter = proof.openGoals().head().node();

        // check if antecedent didn't change
        assertTrue(nodeAfter.sequent().antecedent()
                .equals(nodeBefore.sequent().antecedent()));
        assertTrue(nodeAfter.sequent().succedent().size() == nodeBefore
                .sequent().succedent().size());

        checkJavaBlocks(nodeBefore, nodeAfter);

    }

    @Test
    public void testJoinPointRuleApp() {
        final Proof proof = loadProof(
                "absBlockContract.beforeJoinPointRule.key");

        startAutomaticStrategy(proof);
        assertTrue(proof.openGoals().head().appliedRuleApps().tail()
                .head() instanceof JoinPointBuiltInRuleApp);

        assertTrue(proof.openGoals().head().appliedRuleApps()
                .head() instanceof JoinRuleBuiltInRuleApp);

    }

    @Test
    public void testRemoveJPS() {
        final Proof proof = loadProof("AbsBlockContract.beforeDelete.proof");
        Node nodeBefore = proof.openGoals().head().node();

        startAutomaticStrategy(proof);
        startAutomaticStrategy(proof); 
        startAutomaticStrategy(proof);
        assertTrue(proof.openGoals().head().appliedRuleApps()
                .head() instanceof DeleteJoinPointBuiltInRuleApp);

        Node nodeAfter = proof.openGoals().head().node();

        // check if antecedent didn't change
        assertTrue(nodeAfter.sequent().antecedent()
                .equals(nodeBefore.sequent().antecedent()));
        assertTrue(nodeAfter.sequent().succedent().size() == nodeBefore
                .sequent().succedent().size());

        checkJavaBlocks(nodeAfter, nodeBefore);
    }

    private void checkJavaBlocks(Node withoutJP, Node withJP) {
        for (int i = 0; i < withJP.sequent().succedent().size(); i++) {
            Term termWithoutJP = withoutJP.sequent().succedent().get(i).formula();
            Term termWithJP = withJP.sequent().succedent().get(i).formula();

            if (termWithJP.isContainsJavaBlockRecursive()) {

                if (!JoinRuleUtils.getJavaBlockRecursive(termWithJP).equals(
                        JoinRuleUtils.getJavaBlockRecursive(termWithoutJP))) {

                    JavaProgramElement jPWithoutJP = JoinRuleUtils
                            .getJavaBlockRecursive(termWithoutJP).program();
                    JavaProgramElement jPWithJP = JoinRuleUtils
                            .getJavaBlockRecursive(termWithJP).program();

                    StatementBlock blockWithoutJP = ((StatementBlock) jPWithoutJP)
                            .getInnerMostMethodFrame().getBody();
                    StatementBlock blockWithJP = ((StatementBlock) jPWithJP)
                            .getInnerMostMethodFrame().getBody();

                    assertTrue(blockWithJP
                            .getChildCount() == blockWithoutJP.getChildCount()
                                    + 1);

                    for (int j = 0; j < blockWithoutJP.getChildCount(); j++) {
                        if (!blockWithoutJP.getChildAt(j)
                                .equals(blockWithJP.getChildAt(j))) {
                            assertTrue(blockWithJP.getChildAt(
                                    j) instanceof JoinPointStatement);
                            restIsEqual(blockWithoutJP, blockWithJP, j);
                            break;
                        }
                    }

                }
            }
        }
    }

    private void restIsEqual(StatementBlock blockA,
            StatementBlock blockB, int i) {
        for (int j = i; j < blockA.getChildCount(); j++) {
            assertTrue(blockA.getChildAt(j)
                    .equals(blockB.getChildAt(j + 1)));
        }
    }

    private void startAutomaticStrategy(final Proof proof) {
        ProofStarter starter = new ProofStarter(false);
        starter.init(proof);
        starter.start();
    }

    static Proof loadProof(String proofFileName) {
        File proofFile = new File(TEST_RESOURCES_DIR_PREFIX + proofFileName);
        assertTrue(proofFile.exists());

        try {
            KeYEnvironment<?> environment = KeYEnvironment.load(
                    JavaProfile.getDefaultInstance(), proofFile, null, null,
                    null, true);
            Proof proof = environment.getLoadedProof();
            assertNotNull(proof);

            return proof;
        }
        catch (ProblemLoaderException e) {
            fail("Proof could not be loaded:\n" + e.getMessage());
            return null;
        }
    }

}
