package org.key_project.starvoors.test.testcase;

import java.io.File;
import java.util.HashMap;

import org.junit.Test;
import org.key_project.starvoors.util.StaRVOOrSUtil;

import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;

/**
 * Contains tests for {@link StaRVOOrSUtil}.
 * @author Jesus Mauricio Chimento
 */
public class StaRVOOrSUtilTest extends AbstractSymbolicExecutionTestCase {
   public static final String PLUGIN_PATH_IN_REPOSITORY = "projects/StaRVOOrS/src/tests/org.key_project.starvoors.test/";
   
   /**
    * Tests {@link StaRVOOrSUtil#start(java.io.File)}.
    */
   @Test
   public void testStart() throws Exception {
      HashMap<String, String> originalTacletOptions = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      try {
         File javaFile = new File(keyRepDirectory, PLUGIN_PATH_IN_REPOSITORY + "data/hashtable/HashTable.java");
         // Set expected options
         originalTacletOptions = setDefaultTacletOptions(keyRepDirectory, PLUGIN_PATH_IN_REPOSITORY + "data/hashtable/HashTable.java", "HashTable", "add");
         setOneStepSimplificationEnabled(null, true);
         // Do test
         StaRVOOrSUtil.start(javaFile);
      }
      finally {
         // Restore original options
         setOneStepSimplificationEnabled(null, originalOneStepSimplification);
         restoreTacletOptions(originalTacletOptions);
      }
   }
}
