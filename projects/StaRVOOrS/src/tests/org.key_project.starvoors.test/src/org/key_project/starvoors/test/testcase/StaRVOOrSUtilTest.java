package org.key_project.starvoors.test.testcase;

import java.io.File;

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
      StaRVOOrSUtil.start(new File(keyRepDirectory, PLUGIN_PATH_IN_REPOSITORY + "data/hashtable/HashTable.java"));
   }
}
