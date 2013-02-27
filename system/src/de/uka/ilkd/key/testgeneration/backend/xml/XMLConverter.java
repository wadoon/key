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
import de.uka.ilkd.key.testgeneration.core.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.core.coreinterface.TestCase;
import de.uka.ilkd.key.testgeneration.core.coreinterface.TestSuite;
import de.uka.ilkd.key.testgeneration.core.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelInstance;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelVariable;
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
    private static final XMLEvent newline = eventFactory.createDTD("\n");

    /**
     * {@link XMLEvent} representing a tab.
     */
    private static final XMLEvent tab = eventFactory.createDTD("    ");

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
        } catch (XMLStreamException e) {
            throw new XMLGeneratorException(
                    "FATAL: failed to initialize XMLVisitor" + e.getMessage());
        }
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
    public synchronized String createTestSuite(List<TestCase> testCases,
            boolean format) throws XMLGeneratorException {

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
        } catch (XMLStreamException xse) {
            throw new XMLGeneratorException(xse.getMessage());
        } catch (XMLVisitorException xve) {
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
    private void writeTestCase(TestCase testCase) throws XMLStreamException,
            XMLVisitorException {

        writeStartTag(TESTCASE_ROOT);

        writeMethodInfo(testCase.getMethod());
        writeFixture(testCase.getModel());
        writeOracle(testCase.getOracle());

        writeEndTag(TESTCASE_ROOT);
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
    private void writeOracle(Term oracle) throws XMLVisitorException,
            XMLStreamException {

        OracleVisitor oracleVisitor = new OracleVisitor();
        oracle.execPreOrder(oracleVisitor);
        List<XMLEvent> rawOracleXML = oracleVisitor.getElements();

        writeStartTag(ORACLE_ROOT);
        for (XMLEvent event : rawOracleXML) {
            writeXMLEvent(event);
        }
        writeEndTag(ORACLE_ROOT);
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
    private void writeMethodInfo(KeYJavaMethod method)
            throws XMLStreamException {

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
     * Converts a {@link Model} instance to KeYTestgens native XML format. In
     * the context of the test case itself, this represents the test fixture, or
     * program state prior to the execution of the method.
     * 
     * @param model
     *            the model to convert
     * @throws XMLStreamException
     *             in case the XML could not be generated
     */
    private void writeFixture(Model model) throws XMLStreamException {

        writeStartTag(TESTFIXTURE_ROOT);

        /*
         * Write the variables contained in this fixture
         */
        writeStartTag(VARIABLES_ROOT);
        for (ModelVariable modelVariable : model.getVariables()) {
            writeVariable(modelVariable);
        }
        writeEndTag(VARIABLES_ROOT);

        /*
         * Write the instances contained in this fixture
         */
        writeStartTag(INSTANCES_ROOT);
        for (ModelVariable modelVariable : model.getVariables()) {
            writeInstance(modelVariable.getValue());
        }
        writeEndTag(INSTANCES_ROOT);

        writeEndTag(TESTFIXTURE_ROOT);
    }

    /**
     * Writes an instance of {@link ModelVariable} as XML.
     * 
     * @param variable
     *            the variable to write
     * @throws XMLStreamException
     *             in case the XML could not be generated
     */
    private void writeVariable(ModelVariable variable)
            throws XMLStreamException {

        writeStartTag(VARIABLE_ROOT);

        String identifier = variable.getIdentifier();
        String type = variable.getType();

        /*
         * Write the identifier of this particular variable
         */
        writeStartTag(IDENTIFIER_ROOT);
        writeTextElement(identifier);
        writeEndTag(IDENTIFIER_ROOT);

        /*
         * Write the type of this variable
         */
        writeStartTag(TYPE_ROOT);
        writeTextElement(type);
        writeEndTag(TYPE_ROOT);

        /*
         * Write the instance pointed to by this variable FIXME: Abstraction
         * needs to handle uniqueness in a better way, do not rely on hashCode.
         */
        writeStartTag(VALUE_ROOT);
        writeTextElement(variable.getValue());
        writeEndTag(VALUE_ROOT);

        writeEndTag(VARIABLE_ROOT);
    }

    /**
     * Writes an instance of of some Object to XML
     * 
     * @param instance
     *            the instance to write
     * @throws XMLStreamException
     *             in case the XML could not be generated
     */
    private void writeInstance(Object instance) throws XMLStreamException {

        writeStartTag(INSTANCE_ROOT);

        if (instance instanceof ModelInstance) {
            writeInstance((ModelInstance) instance);
        } else if (instance instanceof Integer) {
            writeInstance((Integer) instance);
        }
        writeEndTag(INSTANCE_ROOT);
    }

    /**
     * Writes an instance of {@link ModelInstance} as XML.
     * 
     * @param instance
     *            the instance to write
     * @throws XMLStreamException
     *             in case the XML could not be generated
     */
    private void writeInstance(ModelInstance instance)
            throws XMLStreamException {

        String identifier = instance.getIdentifier();
        String type = instance.getType();

        /*
         * Write the identifier of the instance
         */
        writeStartTag(IDENTIFIER_ROOT);
        writeTextElement(identifier);
        writeEndTag(IDENTIFIER_ROOT);

        /*
         * Write the type
         */
        writeStartTag(TYPE_ROOT);
        writeTextElement(type);
        writeEndTag(TYPE_ROOT);

        /*
         * Write the fields belonging to this instance
         */
        writeStartTag(FIELD_ROOT);
        for (ModelVariable child : instance.getFields()) {
            writeTextElement(child.getIdentifier());
        }
        writeEndTag(FIELD_ROOT);
    }

    private void writeInstance(Integer instance) throws XMLStreamException {

        String identifier = Integer.toString(instance.hashCode());
        String type = "int";

        /*
         * Write the identifier of the instance
         */
        writeStartTag(IDENTIFIER_ROOT);
        writeTextElement(identifier);
        writeEndTag(IDENTIFIER_ROOT);

        /*
         * Write the type
         */
        writeStartTag(TYPE_ROOT);
        writeTextElement(type);
        writeEndTag(TYPE_ROOT);

        /*
         * Write the fields belonging to this instance
         */
        writeStartTag(FIELD_ROOT);
        writeTextElement(instance.toString());
        writeEndTag(FIELD_ROOT);
    }

    /**
     * Write a preamble for the generated XML document.
     * 
     * @param documentName
     *            the root tag of the document
     * @throws XMLStreamException
     */
    private void writeDocumentStart(String documentName)
            throws XMLStreamException {

        if (format) {
            eventWriter.add(eventFactory.createStartDocument());
            eventWriter.add(newline);
            eventWriter.add(eventFactory.createStartElement("", "",
                    documentName));
            eventWriter.add(newline);
        } else {
            eventWriter.add(eventFactory.createStartDocument());
            eventWriter.add(eventFactory.createStartElement("", "",
                    documentName));
        }
    }

    /**
     * Write the closing section of the document.
     * 
     * @param documentName
     * @throws XMLStreamException
     */
    private void writeDocumentEnd(String documentName)
            throws XMLStreamException {

        if (format) {
            eventWriter
                    .add(eventFactory.createEndElement("", "", documentName));
            eventWriter.add(newline);
            eventWriter.add(eventFactory.createEndDocument());
            eventWriter.add(newline);
        } else {
            eventWriter
                    .add(eventFactory.createEndElement("", "", documentName));
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
        } else {
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
        } else {
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
            eventWriter.add(eventFactory.createCharacters(element.toString()));
            eventWriter.add(newline);
        } else {
            eventWriter.add(eventFactory.createCharacters(element.toString()));
        }
    }

    private void addIndentation() throws XMLStreamException {

        for (int i = 0; i < indentationCounter; i++) {
            eventWriter.add(tab);
        }
    }

    private void writeXMLEvent(XMLEvent event) throws XMLStreamException {

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
        private LinkedList<XMLEvent> elements = new LinkedList<XMLEvent>();

        /**
         * Use a stack in order to properly determine the order in which start
         * and end tags should be inserted for XML elements in the Term.
         */
        private Stack<String> elementNames = new Stack<String>();

        public List<XMLEvent> getElements() {

            return elements;
        }

        /**
         * Generate a textual representation for each relevant node
         */
        @Override
        public void visit(Term visited) {

            Operator operator = visited.op();

            if (operator instanceof LocationVariable
                    || operator instanceof SortDependingFunction
                    || visited.sort() instanceof NullSort) {
                addVariableNode(visited);
            }
        }

        /**
         * Whenever a subtree is entered, create a tag corresponding to the type
         * of the root element, and push the name of the element on the stack in
         * order to later generate an end tag.
         */
        @Override
        public void subtreeEntered(Term subtreeRoot) {

            /*
             * Verify that the operator bound at the current term represents a
             * concept suitable for putting in a tag
             */
            if (isBinaryFunction2(subtreeRoot)) {
                String operatorName = subtreeRoot.op().name().toString();

                XMLEvent startTag = eventFactory.createStartElement("", "",
                        operatorName);
                addTag(startTag);

                elementNames.push(operatorName);
            }
        }

        /**
         * Whenever a subtree is left, generate a closing tag corresponding to
         * the one that was created when the tree was first entered.
         */
        @Override
        public void subtreeLeft(Term subtreeRoot) {

            if (isBinaryFunction2(subtreeRoot)) {
                String operatorName = elementNames.pop();
                XMLEvent endTag = eventFactory.createEndElement("", "",
                        operatorName);
                addTag(endTag);
            }
        }

        /**
         * Add a tag, together with formatting, to the outputStream.
         * 
         * @param tag
         *            the tag to insert
         */
        private void addTag(XMLEvent tag) {

            for (int i = 0; i < elementNames.size(); i++) {
                elements.add(tab);
            }
            elements.add(tag);
            elements.add(newline);
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
        private void addTag(XMLEvent tag, int extraTabs) {

            for (int i = 0; i < extraTabs; i++) {
                elements.add(tab);
            }
            addTag(tag);
        }

        /**
         * Add a node representing a program variable to the outputStream.
         * 
         * @param term
         *            the {@link Term} from which to generate the Node
         */
        private void addVariableNode(Term term) {

            String variableName = resolveIdentifierString(term, SEPARATOR);
            addTag(eventFactory.createCharacters(variableName), 1);
        }
    }

    @Override
    public String convert(TestSuite testSuite) {

        return null;
    }
}