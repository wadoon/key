package org.key_project.starvoors.test.testcase;

import java.io.File;
import java.util.HashMap;

import org.junit.Test;
import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.starvoors.model.io.StaRVOOrSReader;
import org.key_project.starvoors.util.StaRVOOrSUtil;

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
	public void javadl_verification(){
		
	}
	
	
   @Test
   public void testStart_HashTable() throws Exception {
      doTest("data/hashtable/test/HashTable.java",
             "data/hashtable/oracle/HashTable.xml");
   }

   @Test
   public void testStart_ConPurse() throws Exception {
      doTestC("data/conpurse/test/ConPurse.java",
             "data/conpurse/oracle/ConPurse.xml");
   }
   
   protected void doTest(String javaPath, String oraclePath) throws Exception {
      HashMap<String, String> originalTacletOptions = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      try {
         File javaFile = new File(PROJECT_ROOT_DIRECTORY, javaPath);
         assertTrue("Java file '" + javaFile + "' does not exist.", javaFile.exists());
         // Set expected options
         originalTacletOptions = setDefaultTacletOptions(PROJECT_ROOT_DIRECTORY, "data/hashtable/test/HashTable.java", "HashTable", "add");
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
      
      protected void doTestC(String javaPath, String oraclePath) throws Exception {
          HashMap<String, String> originalTacletOptions = null;
          boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
          try {
             File javaFile = new File(PROJECT_ROOT_DIRECTORY, javaPath);
             assertTrue("Java file '" + javaFile + "' does not exist.", javaFile.exists());
             // Set expected options
             originalTacletOptions = setDefaultTacletOptions(PROJECT_ROOT_DIRECTORY, "data/conpurse/test/ConPurse.java", "ConPurse", "startFrom");
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
