package org.key_project.starvoors.test.testcase;

import java.io.File;
import java.util.HashMap;

import org.junit.Test;
import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.starvoors.model.io.StaRVOOrSReader;
import org.key_project.starvoors.util.StaRVOOrSUtil;

import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;

/**
 * Contains tests for {@link StaRVOOrSUtil}.
 * <p>
 * To create new oracle files set
 * {@link AbstractSymbolicExecutionTestCase#CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY}
 * to {@code true}.
 * @author Jesus Mauricio Chimento
 */
public class StaRVOOrSUtilTest extends AbstractStaRVOOrSTest {
   public static final String PLUGIN_PATH_IN_REPOSITORY = "projects/StaRVOOrS/src/tests/org.key_project.starvoors.test/";
   
   /**
    * Tests {@link StaRVOOrSUtil#start(java.io.File)}.
    */
   @Test
   public void testStart() throws Exception {
      doTest("data/hashtable/test/HashTable.java",
             "data/hashtable/oracle/HashTable.xml");
   }
   
   protected void doTest(String javaPath, String oraclePath) throws Exception {
      HashMap<String, String> originalTacletOptions = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      try {
         File javaFile = new File(keyRepDirectory, PLUGIN_PATH_IN_REPOSITORY + javaPath);
         // Set expected options
         originalTacletOptions = setDefaultTacletOptions(keyRepDirectory, PLUGIN_PATH_IN_REPOSITORY + "data/hashtable/test/HashTable.java", "HashTable", "add");
         setOneStepSimplificationEnabled(null, true);
         // Analyze source code
         StaRVOOrSResult result = StaRVOOrSUtil.start(javaFile);
         // Create oracle file if required
         createOracleFile(result, oraclePath);
         // Compare result with oracle file
         File oracleFile = new File(keyRepDirectory, PLUGIN_PATH_IN_REPOSITORY + oraclePath);
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
