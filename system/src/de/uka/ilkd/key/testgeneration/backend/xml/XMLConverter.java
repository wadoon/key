package de.uka.ilkd.key.testgeneration.backend.xml;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

import javax.xml.stream.XMLEventFactory;
import javax.xml.stream.XMLEventWriter;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.events.DTD;
import javax.xml.stream.events.XMLEvent;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.testgeneration.StringConstants;
import de.uka.ilkd.key.testgeneration.backend.IFrameworkConverter;
import de.uka.ilkd.key.testgeneration.backend.custom.ITestCaseParser;
import de.uka.ilkd.key.testgeneration.core.classabstraction.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.core.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelInstance;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelVariable;
import de.uka.ilkd.key.testgeneration.core.testsuiteabstraction.TestCase;
import de.uka.ilkd.key.testgeneration.core.testsuiteabstraction.TestSuite;
import de.uka.ilkd.key.testgeneration.util.parsers.AbstractTermParser;
import de.uka.ilkd.key.testgeneration.util.parsers.visitors.KeYTestGenTermVisitor;
import de.uka.ilkd.key.testgeneration.util.parsers.visitors.XMLVisitorException;

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
     * Instances of this class are used to generate an XML representation from a
     * {@link Term} postcondition.
     * 
     * @author christopher
     */
    private static class OracleVisitor extends KeYTestGenTermVisitor {

        /**
         * Since {@link Visitor} does not support exceptional behavior, whereas
         * the {@link XMLEventWriter} demands it, we use an intermediary buffer
         * to store events, and write them only after the visitation process is
         * completed.
         */
        private final LinkedList<XMLEvent> elements = new LinkedList<XMLEvent>();

        /**
         * Use a stack in order to properly determine the order in which start
         * and end tags should be inserted for XML elements in the Term.
         */
        private final Stack<String> elementNames = new Stack<String>();

        /**
         * Add a tag, together with formatting, to the outputStream.
         * 
         * @param tag
         *            the tag to insert
         */
        private void addTag(final XMLEvent tag) {

            for (int i = 0; i < elementNames.size(); i++) {
                elements.add(XMLConverter.tab);
            }
            elements.add(tag);
            elements.add(XMLConverter.newline);
        }

        /**
         * Add a tag, together with formatting, to the outputstream, indented by
         * a specific number of extra tabs.
         * 
         * @param tag
         *            the tag to insert
         * @param extraTabs
         *            number of extra tabs that should be added to the
         *            indentation of the tag
         */
        private void addTag(final XMLEvent tag, final int extraTabs) {

            for (int i = 0; i < extraTabs; i++) {
                elements.add(XMLConverter.tab);
            }
            addTag(tag);
        }

        /**
         * Add a node representing a program variable to the outputStream.
         * 
         * @param term
         *            the {@link Term} from which to generate the Node
         */
        private void addVariableNode(final Term term) {

            final String variableName = AbstractTermParser
                    .resolveIdentifierString(term, XMLConverter.SEPARATOR);
            addTag(XMLConverter.eventFactory.createCharacters(variableName), 1);
        }

        public List<XMLEvent> getElements() {

            return elements;
        }

        /**
         * Whenever a subtree is entered, create a tag corresponding to the type
         * of the root element, and push the name of the element on the stack in
         * order to later generate an end tag.
         */
        @Override
        public void subtreeEntered(final Term subtreeRoot) {

            /*
             * Verify that the operator bound at the current term represents a
             * concept suitable for putting in a tag
             */
            if (isBinaryFunction2(subtreeRoot)) {
                final String operatorName = subtreeRoot.op().name().toString();

                final XMLEvent startTag = XMLConverter.eventFactory
                        .createStartElement("", "", operatorName);
                addTag(startTag);

                elementNames.push(operatorName);
            }
        }

        /**
         * Whenever a subtree is left, generate a closing tag corresponding to
         * the one that was created when the tree was first entered.
         */
        @Override
        public void subtreeLeft(final Term subtreeRoot) {

            if (isBinaryFunction2(subtreeRoot)) {
                final String operatorName = elementNames.pop();
                final XMLEvent endTag = XMLConverter.eventFactory
                        .createEndElement("", "", operatorName);
                addTag(endTag);
            }
        }

        /**
         * Generate a textual representation for each relevant node
         */
        @Override
        public void visit(final Term visited) {

            final Operator operator = visited.op();

            if (operator instanceof LocationVariable
                    || operator instanceof SortDependingFunction
                    || visited.sort() instanceof NullSort) {
                addVariableNode(visited);
            }
        }
    }

    /**
     * Flag to determine if the XML should be formatted or not.
     */
    private boolean format;

    /**
     * The eventWriter is used to add new {@link XMLEvent}s to the outputStream.
     * These events, in turn, are created by the eventFactory.
     */
    private final XMLEventWriter eventWriter;

    /**
     * The eventFactory is used in order to produce {@link XMLEvent}s, that is,
     * XML tags.
     */
    private static final XMLEventFactory eventFactory = XMLEventFactory
            .newFactory();

    /**
     * The outputStream acts as a buffer for generated XML tags. its content can
     * later be encoded to some other representation, such as a String or File.
     */
    private final OutputStream outputStream = new ByteArrayOutputStream();

    /**
     * {@link XMLEvent} representing a newline.
     */
    private static final XMLEvent newline = XMLConverter.eventFactory
            .createDTD("\n");

    /**
     * {@link XMLEvent} representing a tab.
     */
    private static final XMLEvent tab = XMLConverter.eventFactory
            .createDTD("    ");

    private static final String SEPARATOR = StringConstants.FIELD_SEPARATOR
            .toString();

    /**
     * count the number of indentation tags that should be added before each
     * element in the document.
     */
    private int indentationCounter = 0;

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
            writeInstance(modelVariable.getValue());
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
            writeInstance((ModelInstance) instance);
        } else if (instance instanceof Integer) {
            writeInstance((Integer) instance);
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
     * Writes the {@link Term} AST representing the Oracle of a given test case
     * as XML. To do so, a {@link Visitor} instance is used to walk the AST,
     * substituting concrete names for Terms representing variables in the tree,
     * in order to make things more clean and readable (and more importantly,
     * more easy to refere to for the parser).
     * 
     * @param oracle
     *            the Oracle
     * @throws XMLVisitorException
     *             in case there was a problem during the visitation process
     * @throws XMLStreamException
     *             in case the XML could not be generated
     */
    private void writeOracle(final Term oracle) throws XMLVisitorException,
            XMLStreamException {

        final OracleVisitor oracleVisitor = new OracleVisitor();
        oracle.execPreOrder(oracleVisitor);
        final List<XMLEvent> rawOracleXML = oracleVisitor.getElements();

        writeStartTag(XMLHandler.ORACLE_ROOT);
        for (final XMLEvent event : rawOracleXML) {
            writeXMLEvent(event);
        }
        writeEndTag(XMLHandler.ORACLE_ROOT);
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
        writeOracle(testCase.getOracle());

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
            eventWriter.add(XMLConverter.eventFactory.createCharacters(element
                    .toString()));
            eventWriter.add(XMLConverter.newline);
        } else {
            eventWriter.add(XMLConverter.eventFactory.createCharacters(element
                    .toString()));
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
        final String type = variable.getType();

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

    private void writeXMLEvent(final XMLEvent event) throws XMLStreamException {

        if (event instanceof DTD) {
            if (format) {
                eventWriter.add(event);
            }
        } else {
            indentationCounter++;
            addIndentation();
            indentationCounter--;
            eventWriter.add(event);
        }
    }
}