package org.key_project.starvoors.model.io;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.starvoors.model.StaRVOOrSExecutionPath;
import org.key_project.starvoors.model.StaRVOOrSLoopInvariantApplication;
import org.key_project.starvoors.model.StaRVOOrSMethodContractApplication;
import org.key_project.starvoors.model.StaRVOOrSProof;
import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.XMLUtil;

public class StaRVOOrSWriter {
   public static final String TAG_RESULT = "result";
   public static final String ATTRIBUTE_CONTRACT_ID = "contractId";
   public static final String ATTRIBUTE_CONTRACT_TEXT = "contractText";
   public static final String TAG_EXECUTION_PATH = "executionPath";
   public static final String TAG_PROOF = "proof";
   public static final String ATTRIBUTE_PATH_CONDITION = "pathCondition";
   public static final String ATTRIBUTE_VERIFIED = "verified";
   public static final String ATTRIBUTE_TERMINATION_KIND = "terminationKind";
   public static final String TAG_NOT_FULFILLED_PRECONDITIONS = "notFulfilledPreconditions";
   public static final String TAG_NOT_FULFILLED_NULL_CHECKS = "notFulfilledNullChecks";
   public static final String TAG_NOT_INITIALLY_VALID_LOOP_INVARIANTS = "notInitiallyValidLoopInvariants";
   public static final String TAG_NOT_PRESERVED_LOOP_INVARIANTS = "notPreservedLoopInvariants";
   public static final String TAG_METHOD_CONTRACT_APPLICATION = "methodContractApplication";
   public static final String ATTRIBUTE_FILE = "file";
   public static final String ATTRIBUTE_START_LINE = "startLine";
   public static final String ATTRIBUTE_START_COLUMN = "startColumn";
   public static final String ATTRIBUTE_END_LINE = "endLine";
   public static final String ATTRIBUTE_END_COLUMN = "endColumn";
   public static final String ATTRIBUTE_METHOD = "method";
   public static final String ATTRIBUTE_CONTRACT = "contract";
   public static final String TAG_LOOP_INVARIANT_APPLICATION = "loopInvariant";
   public static final String ATTRIBUTE_TYPE = "type";
   public static final String ATTRIBUTE_TARGET = "target";
   public static final String ATTRIBUTE_NEW_PRECONDITION = "newPrecondition";

   public static void write(StaRVOOrSResult result, File file) throws IOException {
      if (file != null && result != null) {
         IOUtil.writeTo(new FileOutputStream(file), toXML(result, IOUtil.DEFAULT_CHARSET.displayName()));
      }
   }
   
   public static String toXML(StaRVOOrSResult result, String encoding) {
      if (result != null) {
         StringBuffer sb = new StringBuffer();
         XMLUtil.appendXmlHeader(encoding, sb);
         apendResult(0, result, sb);
         return sb.toString();
      }
      else {
         return null;
      }
   }

   private static void apendResult(int level, StaRVOOrSResult result, StringBuffer sb) {
      Map<String, String> attributes = new LinkedHashMap<String, String>();
      XMLUtil.appendStartTag(level, TAG_RESULT, attributes, sb);
      for (StaRVOOrSProof proof : result.getProofs()) {
         appendProof(level + 1, proof, sb);
      }
      XMLUtil.appendEndTag(level, TAG_RESULT, sb);
   }

   private static void appendProof(int level, StaRVOOrSProof proof, StringBuffer sb) {
      Map<String, String> attributes = new LinkedHashMap<String, String>();
      attributes.put(ATTRIBUTE_CONTRACT_ID, proof.getContractId());
      attributes.put(ATTRIBUTE_CONTRACT_TEXT, proof.getContractText());
      attributes.put(ATTRIBUTE_TYPE, proof.getType());
      attributes.put(ATTRIBUTE_TARGET, proof.getTarget());
      XMLUtil.appendStartTag(level, TAG_PROOF, attributes, sb);
      for (StaRVOOrSExecutionPath path : proof.getPaths()) {
         appendPath(level + 1, path, sb);
      }
      XMLUtil.appendEndTag(level, TAG_PROOF, sb);
   }

   private static void appendPath(int level, StaRVOOrSExecutionPath path, StringBuffer sb) {
      Map<String, String> attributes = new LinkedHashMap<String, String>();
      attributes.put(ATTRIBUTE_PATH_CONDITION, path.getPathCondition());
      attributes.put(ATTRIBUTE_VERIFIED, path.isVerified() + "");
      attributes.put(ATTRIBUTE_NEW_PRECONDITION, path.getNewPrecondition());
      if (path.getTerminationKind() != null) {
         attributes.put(ATTRIBUTE_TERMINATION_KIND, path.getTerminationKind().toString());
      }
      XMLUtil.appendStartTag(level, TAG_EXECUTION_PATH, attributes, sb);
      appendMethodContractApplications(level + 1, TAG_NOT_FULFILLED_PRECONDITIONS, path.getNotFulfilledPreconditions(), sb);
      appendMethodContractApplications(level + 1, TAG_NOT_FULFILLED_NULL_CHECKS, path.getNotFulfilledNullChecks(), sb);
      appendLoopInvariantApplications(level + 1, TAG_NOT_INITIALLY_VALID_LOOP_INVARIANTS, path.getNotInitiallyValidLoopInvariants(), sb);
      appendLoopInvariantApplications(level + 1, TAG_NOT_PRESERVED_LOOP_INVARIANTS, path.getNotPreservedLoopInvariants(), sb);
      XMLUtil.appendEndTag(level, TAG_EXECUTION_PATH, sb);
   }

   private static void appendMethodContractApplications(int level,
                                                        String groupTagName,
                                                        StaRVOOrSMethodContractApplication[] applications,
                                                        StringBuffer sb) {
      if (!ArrayUtil.isEmpty(applications)) {
         XMLUtil.appendStartTag(level, groupTagName, Collections.<String, String>emptyMap(), sb);
         for (int i = 0; i < applications.length; i++) {
            StaRVOOrSMethodContractApplication application = applications[i];
            Map<String, String> attributes = new LinkedHashMap<String, String>();
            attributes.put(ATTRIBUTE_FILE, application.getFile());
            attributes.put(ATTRIBUTE_START_LINE, application.getStartLine() + "");
            attributes.put(ATTRIBUTE_START_COLUMN, application.getStartColumn() + "");
            attributes.put(ATTRIBUTE_END_LINE, application.getEndLine() + "");
            attributes.put(ATTRIBUTE_END_COLUMN, application.getEndColumn() + "");
            attributes.put(ATTRIBUTE_TYPE, application.getType());
            attributes.put(ATTRIBUTE_METHOD, application.getMethod());
            attributes.put(ATTRIBUTE_CONTRACT, application.getContract());
            XMLUtil.appendEmptyTag(level + 1, TAG_METHOD_CONTRACT_APPLICATION, attributes, sb);
         }
         XMLUtil.appendEndTag(level, groupTagName, sb);
      }
   }

   private static void appendLoopInvariantApplications(int level,
                                                       String groupTagName,
                                                       StaRVOOrSLoopInvariantApplication[] applications,
                                                       StringBuffer sb) {
      if (!ArrayUtil.isEmpty(applications)) {
         XMLUtil.appendStartTag(level, groupTagName, Collections.<String, String>emptyMap(), sb);
         for (int i = 0; i < applications.length; i++) {
            StaRVOOrSLoopInvariantApplication application = applications[i];
            Map<String, String> attributes = new LinkedHashMap<String, String>();
            attributes.put(ATTRIBUTE_FILE, application.getFile());
            attributes.put(ATTRIBUTE_START_LINE, application.getStartLine() + "");
            attributes.put(ATTRIBUTE_START_COLUMN, application.getStartColumn() + "");
            attributes.put(ATTRIBUTE_END_LINE, application.getEndLine() + "");
            attributes.put(ATTRIBUTE_END_COLUMN, application.getEndColumn() + "");
            XMLUtil.appendEmptyTag(level + 1, TAG_LOOP_INVARIANT_APPLICATION, attributes, sb);
         }
         XMLUtil.appendEndTag(level, groupTagName, sb);
      }
   }
}
