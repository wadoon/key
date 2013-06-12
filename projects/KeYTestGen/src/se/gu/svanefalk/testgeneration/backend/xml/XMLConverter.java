package se.gu.svanefalk.testgeneration.backend.xml;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.util.List;

import javax.xml.stream.XMLEventFactory;
import javax.xml.stream.XMLEventWriter;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.events.XMLEvent;

import se.gu.svanefalk.testgeneration.StringConstants;
import se.gu.svanefalk.testgeneration.backend.IFrameworkConverter;
import se.gu.svanefalk.testgeneration.backend.custom.ITestCaseParser;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaMethod;
import se.gu.svanefalk.testgeneration.core.model.implementation.Model;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelInstance;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelVariable;
import se.gu.svanefalk.testgeneration.core.testsuiteabstraction.TestCase;
import se.gu.svanefalk.testgeneration.core.testsuiteabstraction.TestSuite;
import se.gu.svanefalk.testgeneration.util.visitors.XMLVisitorException;
import de.uka.ilkd.key.logic.op.IProgramVariable;

/**
 * Provides functionality for turning a set of {@link TestCase} instances into a
 * corresponding XML representation. This XML constitutes the default output
 * produced by KeYTestGen2, and can be parsed by instances of
 * {@link ITestCaseParser} in order to generate more specific test suites.
 * 
 * @author christopher
 */
public class XMLConverter extends XMLHandler implements IFrameworkConverter {

    /**
     * The eventFactory is used in order to produce {@link XMLEvent}s, that is,
     * XML tags.
     */
    private static final XMLEventFactory eventFactory = XMLEventFactory.newFactory();

    /**
     * {@link XMLEvent} representing a newline.
     */
    private static final XMLEvent newline = XMLConverter.eventFactory.createDTD("\n");

    private static final String SEPARATOR = StringConstants.FIELD_SEPARATOR.toString();

    /**
     * {@link XMLEvent} representing a tab.
     */
    private static final XMLEvent tab = XMLConverter.eventFactory.createDTD("    ");

    /**
     * The eventWriter is used to add new {@link XMLEvent}s to the outputStream.
     * These events, in turn, are created by the eventFactory.
     */
    private final XMLEventWriter eventWriter;

    /**
     * Flag to determine if the XML should be formatted or not.
     */
    private boolean format;

    /**
     * count the number of indentation tags that should be added before each
     * element in the document.
     */
    private int indentationCounter = 0;

    /**
     * The outputStream acts as a buffer for generated XML tags. its content can
     * later be encoded to some other representation, such as a String or File.
     */
    private final OutputStream outputStream = new ByteArrayOutputStream();

    /**
     * Sets up the XML visitor, initializing the {@link XMLEventWriter} in the
     * process.
     * 
     * @param rootTag
     *            the name of the root tag of the resulting XML document. If
     *            this parameter is null or empty, no root tag will be generated
     *            for the document.
     * @throws XMLGeneratorException
     * @throws XMLVisitorException
     *             in the event that the event writer could not be set up
     */
    public XMLConverter() throws XMLGeneratorException {

        try {
            eventWriter = XMLOutputFactory.newFactory().createXMLEventWriter(
                    outputStream);
        } catch (final XMLStreamException e) {
            throw new XMLGeneratorException(
                    "FATAL: failed to initialize XMLVisitor" + e.getMessage());
        }
    }

    private void addIndentation() throws XMLStreamException {

        for (int i = 0; i < indentationCounter; i++) {
            eventWriter.add(XMLConverter.tab);
        }
    }

    @Override
    public String convert(final TestSuite testSuite) {

        return null;
    }

    /**
     * Create a complete test suite from a set of {@link TestCase} instances,
     * encoded in KeYTestGens native XML format.
     * 
     * @param testCases
     *            the testcases to include in the test suite
     * @param format
     *            add formatting and indentation to the output document?
     * @return an XML representation of the test suite
     * @throws XMLGeneratorException
     *             if XML generation failed
     */
    public synchronized String createTestSuite(final List<TestCase> testCases,
            final boolean format) throws XMLGeneratorException {

        this.format = format;

        try {

            /*
             * Write the preamble for the document
             */
            writeDocumentStart(XMLHandler.TESTSUITE_ROOT);

            /*
             * Write the test cases
             */
            for (final TestCase testCase : testCases) {
                writeTestCase(testCase);
            }

            /*
             * Write the document end
             */
            writeDocumentEnd(XMLHandler.TESTSUITE_ROOT);

            return outputStream.toString();
        } catch (final XMLStreamException xse) {
            throw new XMLGeneratorException(xse.getMessage());
        } catch (final XMLVisitorException xve) {
            throw new XMLGeneratorException(xve.getMessage());
        }
    }

    /**
     * Write the closing section of the document.
     * 
     * @param documentName
     * @throws XMLStreamException
     */
    private void writeDocumentEnd(final String documentName)
            throws XMLStreamException {

        if (format) {
            eventWriter.add(XMLConverter.eventFactory.createEndElement("", "",
                    documentName));
            eventWriter.add(XMLConverter.newline);
            eventWriter.add(XMLConverter.eventFactory.createEndDocument());
            eventWriter.add(XMLConverter.newline);
        } else {
            eventWriter.add(XMLConverter.eventFactory.createEndElement("", "",
                    documentName));
            eventWriter.add(XMLConverter.eventFactory.createEndDocument());
        }
    }

    /**
     * Write a preamble for the generated XML document.
     * 
     * @param documentName
     *            the root tag of the document
     * @throws XMLStreamException
     */
    private void writeDocumentStart(final String documentName)
            throws XMLStreamException {

        if (format) {
            eventWriter.add(XMLConverter.eventFactory.createStartDocument());
            eventWriter.add(XMLConverter.newline);
            eventWriter.add(XMLConverter.eventFactory.createStartElement("",
                    "", documentName));
            eventWriter.add(XMLConverter.newline);
        } else {
            eventWriter.add(XMLConverter.eventFactory.createStartDocument());
            eventWriter.add(XMLConverter.eventFactory.createStartElement("",
                    "", documentName));
        }
    }

    /**
     * Write a closing tag to the stream, i.e. <\"tag">
     * 
     * @param tagName
     *            the name of the tag to write
     * @throws XMLStreamException
     *             in the event there was an error writing the xml
     */
    private void writeEndTag(final String tagName) throws XMLStreamException {

        if (format) {
            addIndentation();
            eventWriter.add(XMLConverter.eventFactory.createEndElement("", "",
                    tagName));
            eventWriter.add(XMLConverter.newline);
            indentationCounter--;
        } else {
            eventWriter.add(XMLConverter.eventFactory.createEndElement("", "",
                    tagName));
        }
    }

    /**
     * Converts a {@link Model} instance to KeYTestgens native XML format. In
     * the context of the test case itself, this represents the test fixture, or
     * program state prior to the execution of the method.
     * 
     * @param model
     *            the model to convert
     * @throws XMLStreamException
     *             in case the XML could not be generated
     */
    private void writeFixture(final Model model) throws XMLStreamException {

        writeStartTag(XMLHandler.TESTFIXTURE_ROOT);

        /*
         * Write the variables contained in this fixture
         */
        writeStartTag(XMLHandler.VARIABLES_ROOT);
        for (final ModelVariable modelVariable : model.getVariables()) {
            writeVariable(modelVariable);
        }
        writeEndTag(XMLHandler.VARIABLES_ROOT);

        /*
         * Write the instances contained in this fixture
         */
        writeStartTag(XMLHandler.INSTANCES_ROOT);
        for (final ModelVariable modelVariable : model.getVariables()) {
            this.writeInstance(modelVariable.getValue());
        }
        writeEndTag(XMLHandler.INSTANCES_ROOT);

        writeEndTag(XMLHandler.TESTFIXTURE_ROOT);
    }

    private void writeInstance(final Integer instance)
            throws XMLStreamException {

        final String identifier = Integer.toString(instance.hashCode());
        final String type = "int";

        /*
         * Write the identifier of the instance
         */
        writeStartTag(XMLHandler.IDENTIFIER_ROOT);
        writeTextElement(identifier);
        writeEndTag(XMLHandler.IDENTIFIER_ROOT);

        /*
         * Write the type
         */
        writeStartTag(XMLHandler.TYPE_ROOT);
        writeTextElement(type);
        writeEndTag(XMLHandler.TYPE_ROOT);

        /*
         * Write the fields belonging to this instance
         */
        writeStartTag(XMLHandler.FIELD_ROOT);
        writeTextElement(instance.toString());
        writeEndTag(XMLHandler.FIELD_ROOT);
    }

    /**
     * Writes an instance of {@link ModelInstance} as XML.
     * 
     * @param instance
     *            the instance to write
     * @throws XMLStreamException
     *             in case the XML could not be generated
     */
    private void writeInstance(final ModelInstance instance)
            throws XMLStreamException {

        final String identifier = instance.getIdentifier();
        final String type = instance.getType();

        /*
         * Write the identifier of the instance
         */
        writeStartTag(XMLHandler.IDENTIFIER_ROOT);
        writeTextElement(identifier);
        writeEndTag(XMLHandler.IDENTIFIER_ROOT);

        /*
         * Write the type
         */
        writeStartTag(XMLHandler.TYPE_ROOT);
        writeTextElement(type);
        writeEndTag(XMLHandler.TYPE_ROOT);

        /*
         * Write the fields belonging to this instance
         */
        writeStartTag(XMLHandler.FIELD_ROOT);
        for (final ModelVariable child : instance.getFields()) {
            writeTextElement(child.getIdentifier());
        }
        writeEndTag(XMLHandler.FIELD_ROOT);
    }

    /**
     * Writes an instance of of some Object to XML
     * 
     * @param instance
     *            the instance to write
     * @throws XMLStreamException
     *             in case the XML could not be generated
     */
    private void writeInstance(final Object instance) throws XMLStreamException {

        writeStartTag(XMLHandler.INSTANCE_ROOT);

        if (instance instanceof ModelInstance) {
            this.writeInstance((ModelInstance) instance);
        } else if (instance instanceof Integer) {
            this.writeInstance((Integer) instance);
        }
        writeEndTag(XMLHandler.INSTANCE_ROOT);
    }

    /**
     * Write the relevant information contained in the {@link KeYJavaMethod}
     * instance belonging to the test case.
     * 
     * @param method
     *            the {@link KeYJavaMethod} instance
     * @throws XMLStreamException
     *             in case the XML could not be generated
     */
    private void writeMethodInfo(final KeYJavaMethod method)
            throws XMLStreamException {

        writeStartTag(XMLHandler.METHOD_ROOT);

        /*
         * Write the name of the method
         */
        writeStartTag(XMLHandler.NAME_ROOT);
        writeTextElement(method.getProgramMethod().getFullName());
        writeEndTag(XMLHandler.NAME_ROOT);

        /*
         * Write the parameters
         */
        writeStartTag(XMLHandler.PARAMETERS_ROOT);
        for (final IProgramVariable parameter : method.getParameters()) {
            writeTextElement(parameter.name().toString());
        }
        writeEndTag(XMLHandler.PARAMETERS_ROOT);

        writeEndTag(XMLHandler.METHOD_ROOT);
    }

    /**
     * Write an opening tag to the stream, i.e. <\"tag">
     * 
     * @param tagName
     *            the name of the tag to write
     * @throws XMLStreamException
     *             in the event there was an error writing the xml
     */
    private void writeStartTag(final String tagName) throws XMLStreamException {

        if (format) {
            indentationCounter++;
            addIndentation();
            eventWriter.add(XMLConverter.eventFactory.createStartElement("",
                    "", tagName));
            eventWriter.add(XMLConverter.newline);
        } else {
            eventWriter.add(XMLConverter.eventFactory.createStartElement("",
                    "", tagName));
        }
    }

    /**
     * Converts a {@link TestCase} instance to KeYTestGens native XML format
     * 
     * @param testCase
     *            the test case to convert
     * @throws XMLStreamException
     *             in case the XML could not be generated
     * @throws XMLVisitorException
     */
    private void writeTestCase(final TestCase testCase)
            throws XMLStreamException, XMLVisitorException {

        writeStartTag(XMLHandler.TESTCASE_ROOT);

        writeMethodInfo(testCase.getMethod());
        writeFixture(testCase.getModel());
        // this.writeOracle(testCase.getOracle());

        writeEndTag(XMLHandler.TESTCASE_ROOT);
    }

    /**
     * Write a text element to the XML stream
     * 
     * @param element
     *            the text element to write
     * @throws XMLStreamException
     *             in the event there was an error writing the XML
     */
    private void writeTextElement(Object element) throws XMLStreamException {

        /*
         * Create a String representation for null objects.
         */
        if (element == null) {
            element = new String("null");
        }

        if (format) {
            indentationCounter++;
            addIndentation();
            indentationCounter--;
            eventWriter.add(XMLConverter.eventFactory.createCharacters(element.toString()));
            eventWriter.add(XMLConverter.newline);
        } else {
            eventWriter.add(XMLConverter.eventFactory.createCharacters(element.toString()));
        }
    }

    /**
     * Writes an instance of {@link ModelVariable} as XML.
     * 
     * @param variable
     *            the variable to write
     * @throws XMLStreamException
     *             in case the XML could not be generated
     */
    private void writeVariable(final ModelVariable variable)
            throws XMLStreamException {

        writeStartTag(XMLHandler.VARIABLE_ROOT);

        final String identifier = variable.getIdentifier();
        final String type = variable.getTypeName();

        /*
         * Write the identifier of this particular variable
         */
        writeStartTag(XMLHandler.IDENTIFIER_ROOT);
        writeTextElement(identifier);
        writeEndTag(XMLHandler.IDENTIFIER_ROOT);

        /*
         * Write the type of this variable
         */
        writeStartTag(XMLHandler.TYPE_ROOT);
        writeTextElement(type);
        writeEndTag(XMLHandler.TYPE_ROOT);

        /*
         * Write the instance pointed to by this variable FIXME: Abstraction
         * needs to handle uniqueness in a better way, do not rely on hashCode.
         */
        writeStartTag(XMLHandler.VALUE_ROOT);
        writeTextElement(variable.getValue());
        writeEndTag(XMLHandler.VALUE_ROOT);

        writeEndTag(XMLHandler.VARIABLE_ROOT);
    }
}