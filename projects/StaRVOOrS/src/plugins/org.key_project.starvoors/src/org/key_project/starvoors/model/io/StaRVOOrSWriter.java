package org.key_project.starvoors.model.io;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.charset.Charset;
import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.starvoors.model.StaRVOOrSExecutionPath;
import org.key_project.starvoors.model.StaRVOOrSProof;
import org.key_project.starvoors.model.StaRVOOrSResult;
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

   public static void write(StaRVOOrSResult result, File file) throws IOException {
      if (file != null && result != null) {
         IOUtil.writeTo(new FileOutputStream(file), toXML(result, Charset.defaultCharset().displayName()));
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
      XMLUtil.appendEmptyTag(level, TAG_EXECUTION_PATH, attributes, sb);
   }
}
