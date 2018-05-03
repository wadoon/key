package org.key_project.starvoors.test.testcase;

import java.io.File;
import java.util.HashMap;

import org.junit.Test;
import org.key_project.starvoors.model.StaRVOOrSProof;
import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.starvoors.model.io.StaRVOOrSReader;
import org.key_project.starvoors.util.StaRVOOrSUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;

/**
 * Contains tests for {@link StaRVOOrSUtil}.
 * <p>
 * To create new oracle files set
 * {@link AbstractSymbolicExecutionTestCase#CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY}
 * to {@code true}.
 * @author Jesus Mauricio Chimento
 */
public class StaRVOOrSUtilTest extends AbstractStaRVOOrSTest {
   /**
    * Tests {@link StaRVOOrSUtil#start(java.io.File)}.
    */
	@Test
	public void testStart_javadl() throws Exception {
		HashMap<String, String> originalTacletOptions = null;
	    boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
	    try {
	       File javaFile = new File(PROJECT_ROOT_DIRECTORY, "data/conpurse/test");
	       File formulae = new File(PROJECT_ROOT_DIRECTORY, "data/formulae");
	       assertTrue("Java file '" + javaFile + "' does not exist.", javaFile.exists());
	       assertTrue("Formula file '" + javaFile + "' does not exist.", formulae.exists());
	       setOneStepSimplificationEnabled(null, true);
	       
	       // Analyze source code
	       File[] content = formulae.listFiles();
	       
	       for (File file : content) {    	  
	     	  KeYEnvironment<?> env = KeYEnvironment.load(file);        	  
	     	  try {     
	     		  Proof proof = env.getLoadedProof();
	     		  System.out.println("Proof in env:\n" + proof.toString());
	     	      try {
	         	      KeYUserProblemFile key = new KeYUserProblemFile(file.getName(),
	         	    		                                          file,
	         	    		                                          new DefaultUserInterfaceControl(),
	         	    		                                          new JavaProfile()); 
               	      key.readProblem();
	         	      System.out.println("KeyFile to string:\n" + key.toString());	  
	         		  System.out.println("Proof obligation:\n" + key.getProofObligation());
	         		  System.out.println();
	         		  assertTrue(key.getProofObligation() != null);
	     	      } catch (ProofInputException e) {
	     	    	  e.printStackTrace();
	     	    	  assertTrue(false);
	     	      }
	     	        catch (Exception e) {
	     	    	  System.out.println("PROBLEM");
	     	    	  assertTrue(false);
	     	      }
	           } finally {
	     	      env.dispose();
	           }	       
	    }
	  } finally {
	       // Restore original options
	       setOneStepSimplificationEnabled(null, originalOneStepSimplification);
	       restoreTacletOptions(originalTacletOptions);
	    }		    
	}
		
   @Test
   public void testStart_HashTable() throws Exception {
      doTest("data/hashtable/test/HashTable.java",
             "data/hashtable/oracle/HashTable.xml",
             "HashTable",
             "add");
   }

   @Test
   public void testStart_ConPurse() throws Exception {
      doTest("data/conpurse/test/ConPurse.java",
             "data/conpurse/oracle/ConPurse.xml",
             "ConPurse",
             "startFrom");
   }
   
   protected void doTest(String javaPath, String oraclePath, String cls, String method) throws Exception {
      HashMap<String, String> originalTacletOptions = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      try {
         File javaFile = new File(PROJECT_ROOT_DIRECTORY, javaPath);
         assertTrue("Java file '" + javaFile + "' does not exist.", javaFile.exists());
         // Set expected options
         originalTacletOptions = setDefaultTacletOptions(PROJECT_ROOT_DIRECTORY, javaPath, cls, method);
         setOneStepSimplificationEnabled(null, true);
         // Analyze source code
         StaRVOOrSResult result = StaRVOOrSUtil.start(javaFile, false, true, true);
         // Create oracle file if required
         createOracleFile(result, oraclePath);
         // Compare result with oracle file
         File oracleFile = new File(PROJECT_ROOT_DIRECTORY, oraclePath);
         StaRVOOrSResult expectedResult = StaRVOOrSReader.load(oracleFile);
         assertResult(expectedResult, result);
      }
      finally {
         // Restore original options
         setOneStepSimplificationEnabled(null, originalOneStepSimplification);
         restoreTacletOptions(originalTacletOptions);
      }
   }
}
