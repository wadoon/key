package org.key_project.starvoors.model.io;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;
import java.util.Deque;
import java.util.LinkedList;

import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.key_project.starvoors.model.StaRVOOrSExecutionPath;
import org.key_project.starvoors.model.StaRVOOrSLoopInvariantApplication;
import org.key_project.starvoors.model.StaRVOOrSMethodContractApplication;
import org.key_project.starvoors.model.StaRVOOrSProof;
import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.util.java.StringUtil;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination.TerminationKind;

public final class StaRVOOrSReader {
   public static StaRVOOrSResult load(File file) throws Exception {
      if (file != null && file.isFile()) {
         return load(new FileInputStream(file));
      }
      else {
         return null;
      }
   }
   
   public static StaRVOOrSResult load(String text) throws Exception {
      if (text != null) {
         return load(new ByteArrayInputStream(text.getBytes()));
      }
      else {
         return null;
      }
   }
   
   public static StaRVOOrSResult load(InputStream in) throws Exception {
      if (in != null) {
         try {
            // Parse XML document
            SAXParserFactory factory = SAXParserFactory.newInstance();
            factory.setNamespaceAware(true);
            SAXParser saxParser = factory.newSAXParser();
            InfoSAXHandler handler = new InfoSAXHandler();
            saxParser.parse(in, handler);
            // Return result
            return handler.getResult();
         }
         finally {
            in.close();
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * Utility class used by {@link StaRVOOrSReader#load(IFile)}.
    * @author Martin Hentschel
    */
   private static class InfoSAXHandler extends DefaultHandler {
      /**
       * The loaded {@link StaRVOOrSResult}.
       */
      private StaRVOOrSResult result;
      
      /**
       * The parent hierarchy filled by {@link #startElement(String, String, String, Attributes)}
       * and emptied by {@link #endElement(String, String, String)}.
       */
      private final Deque<Object> parentStack = new LinkedList<Object>();
      
      /**
       * The currently treated {@link StaRVOOrSExecutionPath}.
       */
      private StaRVOOrSExecutionPath currentPath;

      /**
       * {@inheritDoc}
       */
      @Override
      public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException {
         if (StaRVOOrSWriter.TAG_RESULT.equals(qName)) {
            assertIsTrue(result == null, "Result is already defined.");
            result = new StaRVOOrSResult();
            parentStack.addFirst(result);
         }
         else if (StaRVOOrSWriter.TAG_PROOF.equals(qName)) {
            Object parent = parentStack.peekFirst();
            assertIsTrue(parent == result, parent + " is not the same as " + result);
            StaRVOOrSProof proof = new StaRVOOrSProof(getContractId(attributes), 
                                                      getContractText(attributes),
                                                      getType(attributes),
                                                      getTarget(attributes));
            result.addProof(proof);
            parentStack.addFirst(proof);
         }
         else if (StaRVOOrSWriter.TAG_EXECUTION_PATH.equals(qName)) {
            Object parent = parentStack.peekFirst();
            assertIsTrue(parent instanceof StaRVOOrSProof, parent + " is not a StaRVOOrSProof.");
            StaRVOOrSExecutionPath path = new StaRVOOrSExecutionPath(getPathCondition(attributes), 
                                                                     isVerified(attributes),
                                                                     null,
                                                                     null,
                                                                     null,
                                                                     null,
                                                                     getTerminationKind(attributes));
            ((StaRVOOrSProof) parent).addPath(path);
            currentPath = path;
            parentStack.addFirst(path);
         }
         else if (StaRVOOrSWriter.TAG_NOT_FULFILLED_PRECONDITIONS.equals(qName)) {
            Object parent = parentStack.peekFirst();
            assertIsTrue(parent instanceof StaRVOOrSExecutionPath, parent + " is not a StaRVOOrSExecutionPath.");
            parentStack.addFirst(qName);
         }
         else if (StaRVOOrSWriter.TAG_NOT_FULFILLED_NULL_CHECKS.equals(qName)) {
            Object parent = parentStack.peekFirst();
            assertIsTrue(parent instanceof StaRVOOrSExecutionPath, parent + " is not a StaRVOOrSExecutionPath.");
            parentStack.addFirst(qName);
         }
         else if (StaRVOOrSWriter.TAG_NOT_INITIALLY_VALID_LOOP_INVARIANTS.equals(qName)) {
            Object parent = parentStack.peekFirst();
            assertIsTrue(parent instanceof StaRVOOrSExecutionPath, parent + " is not a StaRVOOrSExecutionPath.");
            parentStack.addFirst(qName);
         }
         else if (StaRVOOrSWriter.TAG_NOT_PRESERVED_LOOP_INVARIANTS.equals(qName)) {
            Object parent = parentStack.peekFirst();
            assertIsTrue(parent instanceof StaRVOOrSExecutionPath, parent + " is not a StaRVOOrSExecutionPath.");
            parentStack.addFirst(qName);
         }
         else if (StaRVOOrSWriter.TAG_METHOD_CONTRACT_APPLICATION.equals(qName)) {
            Object parent = parentStack.peekFirst();
            assertIsTrue(parent instanceof String, parent + " is not a String.");
            assertIsTrue(currentPath != null, "Current Path is not defined.");
            StaRVOOrSMethodContractApplication application = new StaRVOOrSMethodContractApplication(getFile(attributes), 
                                                                                                    getStartLine(attributes), 
                                                                                                    getStartColumn(attributes), 
                                                                                                    getEndLine(attributes), 
                                                                                                    getEndColumn(attributes),
                                                                                                    getType(attributes),
                                                                                                    getMethod(attributes), 
                                                                                                    getContract(attributes));
            if (StaRVOOrSWriter.TAG_NOT_FULFILLED_PRECONDITIONS.equals(parent)) {
               currentPath.addNotFulfilledPrecondition(application);
            }
            else if (StaRVOOrSWriter.TAG_NOT_FULFILLED_NULL_CHECKS.equals(parent)) {
               currentPath.addNotFulfilledNullCheck(application);
            }
            else {
               assertIsTrue(false, "Unsupported parent '" + parent + "'.");
            }
            parentStack.addFirst(application);
         }
         else if (StaRVOOrSWriter.TAG_LOOP_INVARIANT_APPLICATION.equals(qName)) {
            Object parent = parentStack.peekFirst();
            assertIsTrue(parent instanceof String, parent + " is not a String.");
            assertIsTrue(currentPath != null, "Current Path is not defined.");
            StaRVOOrSLoopInvariantApplication application = new StaRVOOrSLoopInvariantApplication(getFile(attributes), 
                                                                                                  getStartLine(attributes), 
                                                                                                  getStartColumn(attributes), 
                                                                                                  getEndLine(attributes), 
                                                                                                  getEndColumn(attributes));
            if (StaRVOOrSWriter.TAG_NOT_INITIALLY_VALID_LOOP_INVARIANTS.equals(parent)) {
               currentPath.addNotInitiallyValidLoopInvariant(application);
            }
            else if (StaRVOOrSWriter.TAG_NOT_PRESERVED_LOOP_INVARIANTS.equals(parent)) {
               currentPath.addNotPreservedLoopInvariant(application);
            }
            else {
               assertIsTrue(false, "Unsupported parent '" + parent + "'.");
            }
            parentStack.addFirst(application);
         }
         else {
            assertIsTrue(false, "Unsupported tag \"" + qName + "\".");
         }
      }

      protected void assertIsTrue(boolean condition, String message) throws SAXException {
         if (!condition) {
            throw new SAXException(message);
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void endElement(String uri, String localName, String qName) throws SAXException {
         if (!parentStack.isEmpty()) {
            parentStack.removeFirst();
         }
      }

      protected String getContractId(Attributes attributes) {
         return attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_CONTRACT_ID);
      }

      protected boolean isVerified(Attributes attributes) {
         String value = attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_VERIFIED);
         return value != null && Boolean.parseBoolean(value);
      }

      protected String getPathCondition(Attributes attributes) {
         return attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_PATH_CONDITION);
      }

      protected String getContractText(Attributes attributes) {
         return attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_CONTRACT_TEXT);
      }

      protected String getType(Attributes attributes) {
         return attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_TYPE);
      }

      protected String getTarget(Attributes attributes) {
         return attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_TARGET);
      }

      protected TerminationKind getTerminationKind(Attributes attributes) {
         String value = attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_TERMINATION_KIND);
         return !StringUtil.isEmpty(value) ? TerminationKind.valueOf(value) : null;
      }

      protected String getFile(Attributes attributes) {
         return attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_FILE);
      }

      protected String getContract(Attributes attributes) {
         return attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_CONTRACT);
      }

      protected String getMethod(Attributes attributes) {
         return attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_METHOD);
      }

      protected int getEndColumn(Attributes attributes) {
         String value = attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_END_COLUMN);
         return value != null ? Integer.parseInt(value) : 0;
      }

      protected int getEndLine(Attributes attributes) {
         String value = attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_END_LINE);
         return value != null ? Integer.parseInt(value) : 0;
      }

      protected int getStartColumn(Attributes attributes) {
         String value = attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_START_COLUMN);
         return value != null ? Integer.parseInt(value) : 0;
      }

      protected int getStartLine(Attributes attributes) {
         String value = attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_START_LINE);
         return value != null ? Integer.parseInt(value) : 0;
      }

      /**
       * Returns the loaded {@link StaRVOOrSResult}.
       * @return The loaded {@link StaRVOOrSResult}.
       */
      public StaRVOOrSResult getResult() {
         return result;
      }
   }
}
