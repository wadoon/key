package org.key_project.starvoors.model.io;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;
import java.util.Deque;
import java.util.LinkedList;

import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.eclipse.core.runtime.Assert;
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
            Assert.isTrue(result == null);
            result = new StaRVOOrSResult();
            parentStack.addFirst(result);
         }
         else if (StaRVOOrSWriter.TAG_PROOF.equals(qName)) {
            Object parent = parentStack.peekFirst();
            Assert.isTrue(parent == result);
            StaRVOOrSProof proof = new StaRVOOrSProof(getContractId(attributes), getContractText(attributes));
            result.addProof(proof);
            parentStack.addFirst(proof);
         }
         else if (StaRVOOrSWriter.TAG_EXECUTION_PATH.equals(qName)) {
            Object parent = parentStack.peekFirst();
            Assert.isTrue(parent instanceof StaRVOOrSProof);
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
            Assert.isTrue(parent instanceof StaRVOOrSExecutionPath);
            parentStack.addFirst(qName);
         }
         else if (StaRVOOrSWriter.TAG_NOT_FULFILLED_NULL_CHECKS.equals(qName)) {
            Object parent = parentStack.peekFirst();
            Assert.isTrue(parent instanceof StaRVOOrSExecutionPath);
            parentStack.addFirst(qName);
         }
         else if (StaRVOOrSWriter.TAG_NOT_INITIALLY_VALID_LOOP_INVARIANTS.equals(qName)) {
            Object parent = parentStack.peekFirst();
            Assert.isTrue(parent instanceof StaRVOOrSExecutionPath);
            parentStack.addFirst(qName);
         }
         else if (StaRVOOrSWriter.TAG_NOT_PRESERVED_LOOP_INVARIANTS.equals(qName)) {
            Object parent = parentStack.peekFirst();
            Assert.isTrue(parent instanceof StaRVOOrSExecutionPath);
            parentStack.addFirst(qName);
         }
         else if (StaRVOOrSWriter.TAG_METHOD_CONTRACT_APPLICATION.equals(qName)) {
            Object parent = parentStack.peekFirst();
            Assert.isTrue(parent instanceof String);
            Assert.isNotNull(currentPath);
            StaRVOOrSMethodContractApplication application = new StaRVOOrSMethodContractApplication(getFile(attributes), 
                                                                                                    getStartLine(attributes), 
                                                                                                    getStartColumn(attributes), 
                                                                                                    getEndLine(attributes), 
                                                                                                    getEndColumn(attributes), 
                                                                                                    getMethod(attributes), 
                                                                                                    getContract(attributes));
            if (StaRVOOrSWriter.TAG_NOT_FULFILLED_PRECONDITIONS.equals(parent)) {
               currentPath.addNotFulfilledPrecondition(application);
            }
            else if (StaRVOOrSWriter.TAG_NOT_FULFILLED_NULL_CHECKS.equals(parent)) {
               currentPath.addNotFulfilledNullCheck(application);
            }
            else {
               Assert.isTrue(false, "Unsupported parent '" + parent + "'.");
            }
            parentStack.addFirst(application);
         }
         else if (StaRVOOrSWriter.TAG_LOOP_INVARIANT_APPLICATION.equals(qName)) {
            Object parent = parentStack.peekFirst();
            Assert.isTrue(parent instanceof String);
            Assert.isNotNull(currentPath);
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
               Assert.isTrue(false, "Unsupported parent '" + parent + "'.");
            }
            parentStack.addFirst(application);
         }
         else {
            Assert.isTrue(false, "Unsupported tag \"" + qName + "\".");
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
