package de.uka.ilkd.key.testgeneration.xml;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.util.List;

import javax.xml.stream.XMLEventFactory;
import javax.xml.stream.XMLEventWriter;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.events.XMLEvent;

import de.uka.ilkd.key.testgeneration.ITestCaseParser;
import de.uka.ilkd.key.testgeneration.TestCase;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.visitors.XMLVisitorException;

/**
 * Provides functionality for turning a set of {@link TestCase} instances into a corresponding XML
 * representation. This XML constitutes the defaul output produced by KeYTestGen2, and can be parsed
 * by instances of {@link ITestCaseParser} in order to generate more specific test suites.
 * 
 * @author christopher
 */
public class XMLGenerator {

    /**
     * The eventWriter is used to add new {@link XMLEvent}s to the outputStream. These events, in
     * turn, are created by the eventFactory.
     */
    private final XMLEventWriter eventWriter;

    /**
     * The outputStream acts as a buffer for generated XML tags. its content can later be encoded to
     * some other representation, such as a String or File.
     */
    private OutputStream outputStream = new ByteArrayOutputStream();

    /**
     * The eventFactory is used in order to produce {@link XMLEvent}s, that is, XML tags.
     */
    private static final XMLEventFactory eventFactory = XMLEventFactory.newFactory();

    /**
     * {@link XMLEvent} representing a newline
     */
    private static final XMLEvent newline = eventFactory.createDTD("\n");

    /**
     * {@link XMLEvent} representing a tab
     */
    private static final XMLEvent tab = eventFactory.createDTD("    ");

    /**
     * Root tag name for a test case
     */
    private final String TESTCASE_ROOT = "testcase";

    /**
     * count the number of indentation tags that should be added before each element in the
     * document.
     */
    private int indentationCounter = 0;

    /**
     * Sets up the XML visitor, initializing the {@link XMLEventWriter} in the process.
     * 
     * @param rootTag
     *            the name of the root tag of the resulting XML document. If this parameter is null
     *            or empty, no root tag will be generated for the document.
     * @throws XMLGeneratorException
     * @throws XMLVisitorException
     *             in the event that the event writer could not be set up
     */
    public XMLGenerator() throws XMLGeneratorException {

        try {
            eventWriter =
                    XMLOutputFactory.newFactory().createXMLEventWriter(outputStream);
        }
        catch (XMLStreamException e) {
            throw new XMLGeneratorException("FATAL: failed to initialize XMLVisitor"
                    + e.getMessage());
        }
    }

    public String createTestSuite(List<TestCase> testCases) throws XMLGeneratorException {

        try {
            /*
             * Write the preamble for the document
             */
            writeDocumentStart("testsuite");

            return null;
        }
        catch (XMLStreamException xse) {
            throw new XMLGeneratorException(xse.getMessage());
        }
    }

    private void writeTestCase(TestCase testCase) throws XMLStreamException {

        KeYJavaMethod method = testCase.getMethod();

        writeStartTag(TESTCASE_ROOT);

        
        
        writeEndTag(TESTCASE_ROOT);

    }

    /**
     * Write a preamble for the generated XML document.
     * 
     * @param documentName
     *            the root tag of the document
     * @throws XMLStreamException
     */
    private void writeDocumentStart(String documentName) throws XMLStreamException {

        eventWriter.add(eventFactory.createStartDocument());
        eventWriter.add(eventFactory.createStartElement("", "", documentName));
    }

    /**
     * Write the closing section of the document.
     * 
     * @param documentName
     * @throws XMLStreamException
     */
    private void writeDocumentEnd(String documentName) throws XMLStreamException {

        eventWriter.add(eventFactory.createEndElement("", "", documentName));
        eventWriter.add(eventFactory.createEndDocument());
    }

    private void writeStartTag(String tagName) throws XMLStreamException {

        indentationCounter++;

        addIndentation();
        eventWriter.add(eventFactory.createStartElement("", "", tagName));
    }

    private void writeEndTag(String tagName) throws XMLStreamException {

        indentationCounter--;

        addIndentation();
        eventWriter.add(eventFactory.createEndElement("", "", tagName));
    }

    private void addIndentation() throws XMLStreamException {

        for (int i = 0; i < indentationCounter; i++) {
            eventWriter.add(tab);
        }
    }
}