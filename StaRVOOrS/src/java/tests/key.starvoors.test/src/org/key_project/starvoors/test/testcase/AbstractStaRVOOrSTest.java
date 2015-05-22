package org.key_project.starvoors.test.testcase;

import java.io.File;
import java.io.IOException;

import org.key_project.starvoors.model.AbstractStaRVOOrSApplication;
import org.key_project.starvoors.model.StaRVOOrSExecutionPath;
import org.key_project.starvoors.model.StaRVOOrSLoopInvariantApplication;
import org.key_project.starvoors.model.StaRVOOrSMethodContractApplication;
import org.key_project.starvoors.model.StaRVOOrSProof;
import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.starvoors.model.io.StaRVOOrSWriter;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;

public abstract class AbstractStaRVOOrSTest extends AbstractSymbolicExecutionTestCase {
   public static final File PROJECT_ROOT_DIRECTORY;

   static {
      File projectRoot = IOUtil.getProjectRoot(StaRVOOrSUtilTest.class);
      // Update path in Eclipse Plug-ins executed as JUnit Test.
      if ("org.key_project.starvoors.test".equals(projectRoot.getName())) {
         projectRoot = projectRoot.getParentFile().getParentFile().getParentFile();
         projectRoot = new File(projectRoot, "java" + File.separator + "tests" + File.separator + "key.starvoors.test");
      }
      // Update path in Eclipse Plug-ins executed as JUnit Plug-in Test.
      else if ("tests".equals(projectRoot.getName())) {
         projectRoot = projectRoot.getParentFile().getParentFile();
         projectRoot = new File(projectRoot, "java" + File.separator + "tests" + File.separator + "key.starvoors.test");
      }
      PROJECT_ROOT_DIRECTORY = new File(projectRoot.getAbsolutePath());
   }
   
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
         if (!StringUtil.equalIgnoreWhiteSpace(expected.getContractText(), actual.getContractText())) {
            assertEquals(expected.getContractText(), actual.getContractText());
         }
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
         assertEquals(expected.getTerminationKind(), actual.getTerminationKind());
         assertMethodContractApplications(expected.getNotFulfilledPreconditions(), actual.getNotFulfilledPreconditions());
         assertMethodContractApplications(expected.getNotFulfilledNullChecks(), actual.getNotFulfilledNullChecks());
         assertLoopInvariantApplications(expected.getNotInitiallyValidLoopInvariants(), actual.getNotInitiallyValidLoopInvariants());
         assertLoopInvariantApplications(expected.getNotPreservedLoopInvariants(), actual.getNotPreservedLoopInvariants());
      }
      else {
         assertNull(actual);
      }
   }

   protected static void assertMethodContractApplications(StaRVOOrSMethodContractApplication[] expected, StaRVOOrSMethodContractApplication[] actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertEquals(expected.length, actual.length);
         for (int i = 0; i < expected.length; i++) {
            assertMethodContractApplication(expected[i], actual[i]);
         }
      }
      else {
         assertNull(actual);
      }
   }

   protected static void assertMethodContractApplication(StaRVOOrSMethodContractApplication expected, StaRVOOrSMethodContractApplication actual) {
      if (expected != null) {
         assertApplication(expected, actual);
         assertEquals(expected.getMethod(), actual.getMethod());
         assertEquals(expected.getContract(), actual.getContract());
      }
      else {
         assertNull(actual);
      }
   }

   protected static void assertLoopInvariantApplications(StaRVOOrSLoopInvariantApplication[] expected, StaRVOOrSLoopInvariantApplication[] actual) {
      if (expected != null) {
         assertNotNull(actual);
         assertEquals(expected.length, actual.length);
         for (int i = 0; i < expected.length; i++) {
            assertLoopInvariantApplication(expected[i], actual[i]);
         }
      }
      else {
         assertNull(actual);
      }
   }

   protected static void assertLoopInvariantApplication(StaRVOOrSLoopInvariantApplication expected, StaRVOOrSLoopInvariantApplication actual) {
      if (expected != null) {
         assertApplication(expected, actual);
      }
      else {
         assertNull(actual);
      }
   }

   protected static void assertApplication(AbstractStaRVOOrSApplication expected, AbstractStaRVOOrSApplication actual) {
      if (expected != null) {
         if (expected.getFile() != null) {
            assertNotNull(actual.getFile());
            // Compare only file names as paths is different on each computer
            String expectedPath = expected.getFile();
            expectedPath = expectedPath.replaceAll("\\\\", File.separator);
            expectedPath = expectedPath.replaceAll("/", File.separator);
            File expectedFile = new File(expectedPath);
            File actualFile = new File(actual.getFile());
            assertEquals(expectedFile.getName(), actualFile.getName());
         }
         else {
            assertNull(actual.getFile());
         }
         assertEquals(expected.getStartLine(), actual.getStartLine());
         assertEquals(expected.getStartColumn(), actual.getStartColumn());
         assertEquals(expected.getEndLine(), actual.getEndLine());
         assertEquals(expected.getEndColumn(), actual.getEndColumn());
      }
      else {
         assertNull(actual);
      }
   }
}
