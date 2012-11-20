package de.uka.ilkd.key.testgeneration.xml;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.util.LinkedList;
import java.util.List;

import javax.xml.stream.XMLEventFactory;
import javax.xml.stream.XMLEventWriter;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.events.DTD;
import javax.xml.stream.events.XMLEvent;

import com.sun.xml.internal.fastinfoset.stax.events.StartElementEvent;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.testgeneration.ITestCaseParser;
import de.uka.ilkd.key.testgeneration.TestCase;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.model.IModel;
import de.uka.ilkd.key.testgeneration.model.IModelVariable;
import de.uka.ilkd.key.testgeneration.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelVariable;
import de.uka.ilkd.key.testgeneration.visitors.TermXMLVisitor;
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
     * Flag to determine if the XML should be formatted or not.
     */
    private boolean format;

    /**
     * The eventWriter is used to add new {@link XMLEvent}s to the outputStream. These events, in
     * turn, are created by the eventFactory.
     */
    private final XMLEventWriter eventWriter;

    /**
     * The outputStream acts as a buffer for generated XML tags. its content can later be encoded to
     * some other representation, such as a String or File.
     */
    private final OutputStream outputStream = new ByteArrayOutputStream();

    private static final List<String> primitiveTypes = new LinkedList<String>();
    static {
        primitiveTypes.add("byte");
        primitiveTypes.add("int");
        primitiveTypes.add("long");
        primitiveTypes.add("boolean");
    }

    /**
     * The eventFactory is used in order to produce {@link XMLEvent}s, that is, XML tags.
     */
    private static final XMLEventFactory eventFactory = XMLEventFactory.newFactory();

    /**
     * {@link XMLEvent} representing a newline.
     */
    private static final XMLEvent newline = eventFactory.createDTD("\n");

    /**
     * {@link XMLEvent} representing a tab.
     */
    private static final XMLEvent tab = eventFactory.createDTD("    ");

    /**
     * Root tag name for a test case.
     */
    private static final String TESTCASE_ROOT = "testcase";

    /**
     * Root tag name for test suites.
     */
    private static final String TESTSUITE_ROOT = "testsuite";

    /**
     * Root tag name for test fixtures.
     */
    private static final String TESTFIXTURE_ROOT = "fixture";

    /**
     * Root tag name for methods.
     */
    private static final String METHOD_ROOT = "method";

    /**
     * Root tag name for names (either for variables or methods).
     */
    private static final String NAME_ROOT = "name";

    /**
     * Root tag name for parameters.
     */
    private static final String PARAMETERS_ROOT = "parameters";

    /**
     * Root tag name for variables
     */
    private static final String VARIABLE_ROOT = "variable";

    /**
     * Root tag name for fields
     */
    private static final String FIELD_ROOT = "field";

    /**
     * Root tag name for the base class
     */
    private static final String SELF_ROOT = "self";

    /**
     * Root tag name for types
     */
    private static final String TYPE_ROOT = "type";

    /**
     * Root tag name for values
     */
    private static final String VALUE_ROOT = "value";

    /**
     * Root tag for oracles
     */
    private static final String ORACLE_ROOT = "oracle";

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

    /**
     * Create a complete test suite from a set of {@link TestCase} instances, encoded in KeYTestGens
     * native XML format.
     * 
     * @param testCases
     *            the testcases to include in the test suite
     * @param format
     *            add formatting and indentation to the output document?
     * @return an XML representation of the test suite
     * @throws XMLGeneratorException
     *             if XML generation failed
     */
    public synchronized String createTestSuite(List<TestCase> testCases, boolean format)
            throws XMLGeneratorException {

        this.format = format;

        try {

            /*
             * Write the preamble for the document
             */
            writeDocumentStart(TESTSUITE_ROOT);

            /*
             * Write the test cases
             */
            for (TestCase testCase : testCases) {
                writeTestCase(testCase);
            }

            /*
             * Write the document end
             */
            writeDocumentEnd(TESTSUITE_ROOT);

            return outputStream.toString();
        }
        catch (XMLStreamException xse) {
            throw new XMLGeneratorException(xse.getMessage());
        }
        catch (XMLVisitorException xve) {
            throw new XMLGeneratorException(xve.getMessage());
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
    private void writeTestCase(TestCase testCase)
            throws XMLStreamException, XMLVisitorException {

        writeStartTag(TESTCASE_ROOT);

        writeMethodInfo(testCase.getMethod());
        writeFixture(testCase.getModel());
        writeOracle(testCase.getOracle());

        writeEndTag(TESTCASE_ROOT);
    }

    private void writeOracle(Term oracle) throws XMLVisitorException, XMLStreamException {

        TermXMLVisitor termXMLVisitor = new TermXMLVisitor(null);
        oracle.execPreOrder(termXMLVisitor);
        List<XMLEvent> rawOracleXML = termXMLVisitor.getRawXML();

        writeStartTag(ORACLE_ROOT);
        for (XMLEvent event : rawOracleXML) {
            writeRawXMLEvent(event);
        }
        writeEndTag(ORACLE_ROOT);
    }

    /**
     * Write the relevant information contained in the {@link KeYJavaMethod} instance belonging to
     * the test case.
     * 
     * @param method
     *            the {@link KeYJavaMethod} instance
     * @throws XMLStreamException
     *             in case the XML could not be generated
     */
    private void writeMethodInfo(KeYJavaMethod method) throws XMLStreamException {

        writeStartTag(METHOD_ROOT);

        /*
         * Write the name of the method
         */
        writeStartTag(NAME_ROOT);
        writeTextElement(method.getProgramMethod().getFullName());
        writeEndTag(NAME_ROOT);

        /*
         * Write the parameters
         */
        writeStartTag(PARAMETERS_ROOT);
        for (IProgramVariable parameter : method.getParameters()) {
            writeTextElement(parameter.name().toString());
        }
        writeEndTag(PARAMETERS_ROOT);

        writeEndTag(METHOD_ROOT);
    }

    /**
     * Converts a {@link Model} instance to KeYTestgens native XML format. In the context of the
     * test case itself, this represents the test fixture, or program state prior to the execution
     * of the method.
     * 
     * @param model
     *            the model to convert
     * @throws XMLStreamException
     *             in case the XML could not be generated
     */
    private void writeFixture(IModel model) throws XMLStreamException {

        writeStartTag(TESTFIXTURE_ROOT);

        for (IModelVariable variable : model.getVariables()) {
            ModelVariable modelVariable = (ModelVariable) variable;

            /*
             * The variable is part of the base class for the method itself, i.e. "self"
             */
            if (modelVariable.getParent() == null && !modelVariable.isStatic()) {
                writeStartTag(SELF_ROOT);
                writeVariable(modelVariable);
                writeEndTag(SELF_ROOT);
            }

            /*
             * The variable is static, and part either of self or some other class
             */
        }

        writeEndTag(TESTFIXTURE_ROOT);

    }

    private void writeVariable(ModelVariable variable) throws XMLStreamException {

        writeStartTag(VARIABLE_ROOT);

        String variableName = variable.getName();
        String variableType = variable.getType();

        /*
         * Write the name of the variable
         */
        writeStartTag(NAME_ROOT);
        writeTextElement(variableName);
        writeEndTag(NAME_ROOT);

        /*
         * Write the type
         */
        writeStartTag(TYPE_ROOT);
        writeTextElement(variableType);
        writeEndTag(TYPE_ROOT);

        /*
         * Distinguish between primitive and reference types here - a primitive type will only have
         * a value, whereas a reference type will have a set of fields instead. Create output
         * appropriately.
         */
        if (primitiveTypes.contains(variableType)) {

            writeStartTag(VALUE_ROOT);
            writeTextElement(variable.getValue().toString());
            writeEndTag(VALUE_ROOT);
        }
        else {
            writeStartTag(FIELD_ROOT);
            for (ModelVariable child : variable.getChildren()) {
                writeVariable(child);
            }
            writeEndTag(FIELD_ROOT);
        }

        writeEndTag(VARIABLE_ROOT);
    }

    /**
     * Write a preamble for the generated XML document.
     * 
     * @param documentName
     *            the root tag of the document
     * @throws XMLStreamException
     */
    private void writeDocumentStart(String documentName) throws XMLStreamException {

        if (format) {
            eventWriter.add(eventFactory.createStartDocument());
            eventWriter.add(newline);
            eventWriter.add(eventFactory.createStartElement("", "", documentName));
            eventWriter.add(newline);
        }
        else {
            eventWriter.add(eventFactory.createStartDocument());
            eventWriter.add(eventFactory.createStartElement("", "", documentName));
        }
    }

    /**
     * Write the closing section of the document.
     * 
     * @param documentName
     * @throws XMLStreamException
     */
    private void writeDocumentEnd(String documentName) throws XMLStreamException {

        if (format) {
            eventWriter.add(eventFactory.createEndElement("", "", documentName));
            eventWriter.add(newline);
            eventWriter.add(eventFactory.createEndDocument());
            eventWriter.add(newline);
        }
        else {
            eventWriter.add(eventFactory.createEndElement("", "", documentName));
            eventWriter.add(eventFactory.createEndDocument());
        }
    }

    /**
     * Write an opening tag to the stream, i.e. <\"tag">
     * 
     * @param tagName
     *            the name of the tag to write
     * @throws XMLStreamException
     *             in the event there was an error writing the xml
     */
    private void writeStartTag(String tagName) throws XMLStreamException {

        if (format) {
            indentationCounter++;
            addIndentation();
            eventWriter.add(eventFactory.createStartElement("", "", tagName));
            eventWriter.add(newline);
        }
        else {
            eventWriter.add(eventFactory.createStartElement("", "", tagName));
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
    private void writeEndTag(String tagName) throws XMLStreamException {

        if (format) {
            addIndentation();
            eventWriter.add(eventFactory.createEndElement("", "", tagName));
            eventWriter.add(newline);
            indentationCounter--;
        }
        else {
            eventWriter.add(eventFactory.createEndElement("", "", tagName));
        }
    }

    /**
     * Write a text element to the XML stream
     * 
     * @param element
     *            the text element to write
     * @throws XMLStreamException
     *             in the event there was an error writing the XML
     */
    private void writeTextElement(String element) throws XMLStreamException {

        if (format) {
            indentationCounter++;
            addIndentation();
            indentationCounter--;

            eventWriter.add(eventFactory.createCharacters(element));
            eventWriter.add(newline);
        }
        else {
            eventWriter.add(eventFactory.createCharacters(element));
        }
    }

    private void addIndentation() throws XMLStreamException {

        for (int i = 0; i < indentationCounter; i++) {
            eventWriter.add(tab);
        }
    }

    private void writeRawXMLEvent(XMLEvent event) throws XMLStreamException {

        if (event instanceof DTD) {
            if (format) {
                eventWriter.add(event);
            }
        }
        else {
            indentationCounter++;
            addIndentation();
            indentationCounter--;
            eventWriter.add(event);
        }
    }
}