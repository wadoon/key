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
import org.key_project.starvoors.model.StaRVOOrSProof;
import org.key_project.starvoors.model.StaRVOOrSResult;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

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
            StaRVOOrSExecutionPath path = new StaRVOOrSExecutionPath(getPathCondition(attributes), isVerified(attributes));
            ((StaRVOOrSProof) parent).addPath(path);
            parentStack.addFirst(path);
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

      public String getContractId(Attributes attributes) {
         return attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_CONTRACT_ID);
      }

      public boolean isVerified(Attributes attributes) {
         String value = attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_VERIFIED);
         return value != null && Boolean.parseBoolean(value);
      }

      public String getPathCondition(Attributes attributes) {
         return attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_PATH_CONDITION);
      }

      public String getContractText(Attributes attributes) {
         return attributes.getValue(StaRVOOrSWriter.ATTRIBUTE_CONTRACT_TEXT);
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
