package de.uka.ilkd.key.rule.join;

import java.io.File;

import org.junit.Test;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.JoinPointStatement;
import de.uka.ilkd.key.logic.JavaBlock;
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
        
    }

    @Test
    public void testITE() {
        final Proof proof = loadProof("Gcd.ITE.open.key");
        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }

    @Test
    public void testPredicateAbstraction() {
        final Proof proof = loadProof(
                "Gcd.predAbstr.key");
        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }


    @Test
    public void testNestedMergeBlockContract1() {
        final Proof proof = loadProof("Math_notNull.nested.key");
        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }

    @Test
    public void testNestedMergeBlockContract2() {
        final Proof proof = loadProof("Math_notNull.nested.2.key");
        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }
    
    @Test
    public void testTryInsideContract(){
        final Proof proof = loadProof("Math_divContract.key");
        //doesn't close at the first attempt
        startAutomaticStrategy(proof);
        assertFalse(proof.closed());
        //without doing anything special, the proof closed at the second attempt.
        startAutomaticStrategy(proof);
        assertTrue(proof.closed());
    }

    @Test
    public void testAddJPS() {
        //For this example the max. number of steps is set to 1
        final Proof proof = loadProof(
                "absBlockContract.addJoinPointStatement.key");

        Node nodeBefore = proof.openGoals().head().node();

        startAutomaticStrategy(proof);

        assertTrue(proof.openGoals().head().appliedRuleApps()
                .head() instanceof BlockContractBuiltInRuleApp);
       SourceElement jB = JavaTools.getActiveStatement(JoinRuleUtils.getJavaBlockRecursive(proof.openGoals().head().appliedRuleApps()
               .head().posInOccurrence().subTerm()));
        
        
        Node nodeAfter = proof.openGoals().head().node();

        // check if antecedent didn't change
        assertTrue(nodeAfter.sequent().antecedent()
                .equals(nodeBefore.sequent().antecedent()));
        assertTrue(nodeAfter.sequent().succedent().size() == nodeBefore
                .sequent().succedent().size());
 
        StatementBlock blockWithoutJP = ((StatementBlock)JoinRuleUtils
                .getJavaBlockRecursive(nodeBefore.sequent().succedent().get(1)
                        .formula()).program())
                .getInnerMostMethodFrame().getBody();
        
        StatementBlock blockWithJP = ((StatementBlock) JoinRuleUtils
                .getJavaBlockRecursive(nodeAfter.sequent().succedent().get(1)
                        .formula()).program())
                .getInnerMostMethodFrame().getBody();

        assertTrue(((StatementBlock) blockWithJP.getChildAt(0)).getChildAt(1).equals(blockWithoutJP.getChildAt(0)));
        assertTrue(((StatementBlock) blockWithJP.getChildAt(0)).getChildAt(2) instanceof JoinPointStatement);

        for (int j = 1; j < blockWithoutJP.getChildCount(); j++) {
            assertTrue(blockWithJP.getChildAt(j).equals(blockWithoutJP.getChildAt(j)));
        }

    }


//    @Test
//    public void testRemoveJPS() {
//        //For this example the max. number of steps ist set to 1
//        final Proof proof = loadProof("AbsBlockContract.beforeDelete.proof");
//        Node nodeBefore = proof.openGoals().head().node();
//        startAutomaticStrategy(proof);
//        assertTrue(proof.openGoals().head().appliedRuleApps()
//                .head() instanceof DeleteJoinPointBuiltInRuleApp);
//
//        Node nodeAfter = proof.openGoals().head().node();
//
//        // check if antecedent didn't change
//        assertTrue(nodeAfter.sequent().antecedent()
//                .equals(nodeBefore.sequent().antecedent()));
//        assertTrue(nodeAfter.sequent().succedent().size() == nodeBefore
//                .sequent().succedent().size());
//        
//        JavaBlock javaBlockAfter = JoinRuleUtils
//                .getJavaBlockRecursive(nodeAfter.sequent().succedent().get(0)
//                        .formula());
//        
//        StatementBlock blockWithoutJP = ((StatementBlock) javaBlockAfter.program())
//                .getInnerMostMethodFrame().getBody();
//        StatementBlock blockWithJP = ((StatementBlock) JoinRuleUtils
//                .getJavaBlockRecursive(nodeBefore.sequent().succedent().get(0)
//                        .formula()).program())
//                .getInnerMostMethodFrame().getBody();
//
//        assertTrue(JavaTools.getActiveStatement(javaBlockAfter).equals(new StatementBlock()));
//
//        for (int j = 1; j < blockWithoutJP.getChildCount(); j++) {
//            assertTrue(blockWithJP.getChildAt(j).equals(blockWithoutJP.getChildAt(j)));
//        }
//
//    }

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
