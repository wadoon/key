package org.key_project.starvoors.test.testcase;

import java.io.File;
import java.io.IOException;

import org.key_project.starvoors.model.StaRVOOrSExecutionPath;
import org.key_project.starvoors.model.StaRVOOrSProof;
import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.starvoors.model.io.StaRVOOrSWriter;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;

public abstract class AbstractStaRVOOrSTest extends AbstractSymbolicExecutionTestCase {
   protected void createOracleFile(StaRVOOrSResult result, String oraclePathInBaseDirFile) throws IOException {
      if (tempNewOracleDirectory != null && tempNewOracleDirectory.isDirectory()) {
         // Create sub folder structure
         File oracleFile = new File(tempNewOracleDirectory, oraclePathInBaseDirFile);
         oracleFile.getParentFile().mkdirs();
         // Create oracle file
         StaRVOOrSWriter.write(result, oracleFile);
         // Print message to the user.
         printOracleDirectory();
      }
   }
   
   protected static void assertResult(StaRVOOrSResult expected, StaRVOOrSResult actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertProofs(expected.getProofs(), actual.getProofs());
      }
      else {
         assertNull(actual);
      }
   }

   protected static void assertProofs(StaRVOOrSProof[] expected, StaRVOOrSProof[] actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertEquals(expected.length, actual.length);
         for (int i = 0; i < expected.length; i++) {
            assertProof(expected[i], actual[i]);
         }
      }
      else {
         assertNull(actual);
      }
   }

   protected static void assertProof(StaRVOOrSProof expected, StaRVOOrSProof actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertEquals(expected.getContractId(), actual.getContractId());
         TestUtilsUtil.assertEqualsIgnoreWhitespace(expected.getContractText(), actual.getContractText());
         assertPaths(expected.getPaths(), actual.getPaths());
      }
      else {
         assertNull(actual);
      }
   }

   protected static void assertPaths(StaRVOOrSExecutionPath[] expected, StaRVOOrSExecutionPath[] actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertEquals(expected.length, actual.length);
         for (int i = 0; i < expected.length; i++) {
            assertPath(expected[i], actual[i]);
         }
      }
      else {
         assertNull(actual);
      }
   }

   protected static void assertPath(StaRVOOrSExecutionPath expected, StaRVOOrSExecutionPath actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertEquals(expected.getPathCondition(), actual.getPathCondition());
         assertEquals(expected.isVerified(), actual.isVerified());
         assertEquals(expected.isAllPreconditionsFulfilled(), actual.isAllPreconditionsFulfilled());
         assertEquals(expected.isAllNotNullChecksFulfilled(), actual.isAllNotNullChecksFulfilled());
         assertEquals(expected.isAllLoopInvariantsInitiallyFulfilled(), actual.isAllLoopInvariantsInitiallyFulfilled());
         assertEquals(expected.isAllLoopInvariantsPreserved(), actual.isAllLoopInvariantsPreserved());
      }
      else {
         assertNull(actual);
      }
   }
}
