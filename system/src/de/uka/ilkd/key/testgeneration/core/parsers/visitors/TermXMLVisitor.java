package de.uka.ilkd.key.testgeneration.core.parsers.visitors;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.util.LinkedList;
import java.util.Stack;

import javax.xml.stream.XMLEventFactory;
import javax.xml.stream.XMLEventWriter;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.events.XMLEvent;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.testgeneration.StringConstants;
import de.uka.ilkd.key.testgeneration.core.parsers.AbstractTermParser;

/**
 * Generates an XML representation for a {@link Term}.
 * 
 * @author christopher
 */
public class TermXMLVisitor extends KeYTestGenTermVisitor {

    /**
     * The name of the root tag of the XML document. If null or empty, it is
     * excluded altogether
     */
    private final String rootTag;

    /**
     * Since {@link Visitor} does not support exceptional behavior, whereas the
     * {@link XMLEventWriter} demands it, we use an intermediary buffer to store
     * events, and write them only after the visitation process is completed.
     */
    private LinkedList<XMLEvent> elements = new LinkedList<XMLEvent>();

    /**
     * Use a stack in order to properly determine the order in which start and
     * end tags should be inserted for XML elements in the Term.
     */
    private Stack<String> elementNames = new Stack<String>();

    /**
     * The outputStream acts as a buffer for generated XML tags. its content can
     * later be encoded to some other representation, such as a String or File.
     */
    private OutputStream outputStream = new ByteArrayOutputStream();

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

    private static final String SEPARATOR = StringConstants.FIELD_SEPARATOR
            .toString();

    /**
     * {@link XMLEvent} representing a newline
     */
    private static final XMLEvent newline = eventFactory.createDTD("\n");

    /**
     * {@link XMLEvent} representing a tab
     */
    private static final XMLEvent tab = eventFactory.createDTD("    ");

    /**
     * Sets up the XML visitor, initializing the {@link XMLEventWriter} in the
     * process.
     * 
     * @param rootTag
     *            the name of the root tag of the resulting XML document. If
     *            this parameter is null or empty, no root tag will be generated
     *            for the document.
     * @throws XMLVisitorException
     *             in the event that the event writer could not be set up
     */
    public TermXMLVisitor(String rootTag) throws XMLVisitorException {

        try {
            eventWriter = XMLOutputFactory.newFactory().createXMLEventWriter(
                    outputStream);
        } catch (XMLStreamException e) {
            throw new XMLVisitorException(
                    "FATAL: failed to initialize XMLVisitor", e);
        }

        this.rootTag = rootTag;
    }

    /**
     * Get the raw list of {@link XMLEvent}, suitable for external processing.
     * 
     * @return
     */
    public LinkedList<XMLEvent> getRawXML() {

        return elements;
    }

    /**
     * Retrieves the (formatted) XML document created during the visitation
     * process as a String.
     * 
     * @return the XML document as a String
     * @throws XMLVisitorException
     *             in the event that there was as problem writing to the XML
     *             stream, and hence the document could not be created.
     */
    public String getXMLAsString() throws XMLVisitorException {

        try {

            /*
             * Add a standard header for the resulting XML document
             */
            eventWriter.add(eventFactory.createStartDocument());
            eventWriter.add(newline);

            /*
             * Add the starting root tag, assuming it is not empty or null
             */
            if (rootTag != null && !rootTag.isEmpty()) {
                eventWriter.add(eventFactory
                        .createStartElement("", "", rootTag));
                eventWriter.add(newline);
            }

            /*
             * Write each buffered XMLElement to the actual XML stream
             */
            while (!elements.isEmpty()) {
                XMLEvent next = elements.poll();
                eventWriter.add(next);
            }

            /*
             * Add the ending root tag, assuming it is not empty or null
             */
            if (rootTag != null && !rootTag.isEmpty()) {
                eventWriter.add(eventFactory.createEndElement("", "", rootTag));
            }

            eventWriter.add(eventFactory.createEndDocument());
        } catch (XMLStreamException xse) {
            throw new XMLVisitorException(
                    "FATAL: there was an error writing to the XML stream: "
                            + xse.getMessage(), xse);
        }

        /*
         * Finally, return the XML document as a String
         */
        return outputStream.toString();
    }

    /**
     * Generate a textual representation for each relevant node
     */
    @Override
    public void visit(Term visited) {

        System.out.println("TERM: " + visited);
        System.out.println("OPERATOR: " + visited.op().getClass());
        /*
         * Output text only if the node contains something suitable, i.e. it is
         * not a Junctor or other composite operation, but an actual value.
         */
        if (isBinaryFunction2(visited)) {
            return;
        }

        Operator operator = visited.op();

        /*
         * TODO: Make polymorphic
         */

        if (operator instanceof LocationVariable
                || operator instanceof SortDependingFunction) {
            addVariableNode(visited);
        } else {
            addTag(eventFactory.createStartElement("", "", "field"));
            addTag(eventFactory.createCharacters(visited.toString()), 1);
            addTag(eventFactory.createEndElement("", "", "field"));
        }
    }

    /**
     * Whenever a subtree is entered, create a tag corresponding to the type of
     * the root element, and push the name of the element on the stack in order
     * to later generate an end tag.
     */
    @Override
    public void subtreeEntered(Term subtreeRoot) {

        /*
         * Verify that the operator bound at the current term represents a
         * concept suitable for putting in a tag
         */
        if (!isBinaryFunction2(subtreeRoot)) {
            return;
        }

        String operatorName = subtreeRoot.op().name().toString();

        XMLEvent startTag = eventFactory.createStartElement("", "",
                operatorName);
        addTag(startTag);

        elementNames.push(operatorName);
    }

    /**
     * Whenever a subtree is left, generate a closing tag corresponding to the
     * one that was created when the tree was first entered.
     */
    @Override
    public void subtreeLeft(Term subtreeRoot) {

        if (!isBinaryFunction2(subtreeRoot)) {
            return;
        }

        String operatorName = elementNames.pop();

        XMLEvent endTag = eventFactory.createEndElement("", "", operatorName);
        addTag(endTag);

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
     * Add a tag, together with formatting, to the outputstream, indented by a
     * specific number of extra tabs.
     * 
     * @param tag
     *            the tag to insert
     * @param extraTabs
     *            number of extra tabs that should be added to the indentation
     *            of the tag
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

        addTag(eventFactory.createStartElement("", "", "field"));
        addTag(eventFactory.createCharacters(variableName), 1);
        addTag(eventFactory.createEndElement("", "", "field"));
    }
}
