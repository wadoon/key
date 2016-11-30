package de.uka.ilkd.key.rule.join;

import java.io.File;

import org.junit.Test;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.JoinPointStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.BlockContractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BlockContractRule;
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
        final Proof proof = loadProof("absBlockContract.key");
        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }

    @Test
    public void testAddJPS() {
        final Proof proof = loadProof(
                "absBlockContract.addJoinPointStatement.key");

        Node nodeBefore = proof.openGoals().head().node();

        startAutomaticStrategyOneStep(proof);
        assertTrue(proof.openGoals().head().appliedRuleApps()
                .head() instanceof BlockContractBuiltInRuleApp);

        Node nodeAfter = proof.openGoals().head().node();

        // check if antecedent didn't change
        assertTrue(nodeAfter.sequent().antecedent()
                .equals(nodeBefore.sequent().antecedent()));
        assertTrue(nodeAfter.sequent().succedent().size() == nodeBefore
                .sequent().succedent().size());
        
        checkJavaBlocks(nodeAfter, nodeBefore);

    }
    
    @Test
    public void testRemoveJPS() {
        final Proof proof = loadProof("absBlockContract.beforeDelete.key");
        Node nodeBefore = proof.openGoals().head().node();

        startAutomaticStrategyOneStep(proof);
        assertTrue(proof.openGoals().head().appliedRuleApps()
                .head() instanceof DeleteJoinPointBuiltInRuleApp);

        Node nodeAfter = proof.openGoals().head().node();

        // check if antecedent didn't change
        assertTrue(nodeAfter.sequent().antecedent()
                .equals(nodeBefore.sequent().antecedent()));
        assertTrue(nodeAfter.sequent().succedent().size() == nodeBefore
                .sequent().succedent().size());
        
        checkJavaBlocks(nodeBefore, nodeAfter);
    }
    
    private void checkJavaBlocks(Node a, Node b){
        for (int i = 0; i < b.sequent().succedent().size(); i++) {
            Term termA = a.sequent().succedent().get(i).formula();
            Term termB = b.sequent().succedent().get(i).formula();
            
            if (termB.isContainsJavaBlockRecursive()) {

                if (!JoinRuleUtils.getJavaBlockRecursive(termB).equals(
                        JoinRuleUtils.getJavaBlockRecursive(termA))) {
                    
                    JavaProgramElement jPA = JoinRuleUtils
                            .getJavaBlockRecursive(termA).program();
                    JavaProgramElement jPB = JoinRuleUtils
                            .getJavaBlockRecursive(termB).program();
                    
                    ImmutableArray<? extends Statement> bodyA = ((StatementBlock) jPA)
                            .getBody();
                    ImmutableArray<? extends Statement> bodyB = ((StatementBlock) jPB)
                            .getBody();
                    
                    StatementBlock innerBlockA = ((MethodFrame) bodyA
                            .get(0).getFirstElement()).getBody();
                    StatementBlock innerBlockB= ((MethodFrame) bodyB
                            .get(0).getFirstElement()).getBody();
                    
                    assertTrue(innerBlockA
                            .getChildCount() == innerBlockB.getChildCount()
                                    + 1);

                    for (int j = 0; j < innerBlockA.getChildCount(); j++) {
                        if (!innerBlockB.getChildAt(i)
                                .equals(innerBlockB.getChildAt(i))) {
                            assertTrue(innerBlockA
                                    .getChildAt(i) instanceof JoinPointStatement
                                    || innerBlockB.getChildAt(
                                            i) instanceof JoinPointStatement);
                            checkTheRest(innerBlockA, innerBlockB, i);
                            break;
                        }
                    }

                }
            }
        }
    }

    private void checkTheRest(StatementBlock innerBlockAfter,
            StatementBlock innerBlockBefore, int i) {
        for (int j = i; j < innerBlockBefore.getChildCount(); j++) {
            assertTrue(innerBlockAfter.getChildAt(j + 1)
                    .equals(innerBlockBefore.getChildAt(j)));
        }
    }

    private void startAutomaticStrategy(final Proof proof) {
        ProofStarter starter = new ProofStarter(false);
        starter.init(proof);
        starter.start();
    }

    private void startAutomaticStrategyOneStep(final Proof proof) {
        ProofStarter starter = new ProofStarter(false);
        starter.setMaxRuleApplications(1);
        starter.init(proof);
        starter.start();
        // .head().posInOccurrence().subTerm();

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
