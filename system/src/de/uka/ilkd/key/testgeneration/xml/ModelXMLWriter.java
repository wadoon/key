package de.uka.ilkd.key.testgeneration.xml;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.text.ParseException;

import javax.xml.stream.XMLEventFactory;
import javax.xml.stream.XMLEventWriter;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.events.XMLEvent;

import de.uka.ilkd.key.testgeneration.model.IModel;

/**
 * Encapsulates the functionality needed to translate a model into a standard
 * XML representation. The associated schema is TestCase.xsd, with related
 * schema JavaClass.xsd.
 * 
 * @author christopher
 * 
 */
public class ModelXMLWriter {

    XMLEventFactory eventFactory = XMLEventFactory.newFactory();
    XMLOutputFactory outputFactory = XMLOutputFactory.newFactory();

    XMLEventWriter eventWriter;

    /*
     * Standard elements representing newlines and tabs, necessary for
     * formatting the XML, in the event that the user wants to print it to a
     * file.
     */
    XMLEvent newline = eventFactory.createDTD("\n");
    XMLEvent tab = eventFactory.createDTD("\t");

    /**
     * Parse the model returned by the SMT solver, together with the surrounding
     * context of the method, turning everything into a final test suite.
     * 
     * @return
     * @throws XMLGeneratorException
     * @throws ParseException
     * @throws XMLStreamException
     */
    public String generateXML(IModel model) throws XMLGeneratorException,
            ParseException {

        OutputStream output = new ByteArrayOutputStream();

        try {
            eventWriter = outputFactory.createXMLEventWriter(output);

            /*
             * Begin constructing the XML tree - set up the basic preamble, and
             * begin the exploration and parsing process.
             */
            eventWriter.add(eventFactory.createStartDocument());
            eventWriter.add(newline);

            /*
             * Set up the precondition (or test fixture) for the execution path
             * covered by the current test case. This should be extractable in
             * whole from the symbolic execution environment and the model we
             * have generated.
             * 
             * TODO: There is very much to refine here
             * 
             * We iterate over the model for the node we are generating a test
             * case for, and set up the relevant variables accordingly.
             * 
             * TODO: how do we distinguish between local variables and variables
             * declared outside the method body of the IUT?
             */
            /*
            for (IModelContainer container : model) {

                createFieldNode(container);
            }*/
        } catch (XMLStreamException xse) {

            throw new XMLGeneratorException(xse.getMessage());
        }
        return output.toString();
    }

    /*
    private void createFieldNode(IModelContainer valueContainer) {

    }

    private void createNode(String name, String value)
            throws XMLStreamException {
        eventWriter.add(tab);
        eventWriter.add(eventFactory.createStartElement("", "", name));
        eventWriter.add(eventFactory.createCharacters(value.toString()));
        eventWriter.add(eventFactory.createEndElement("", "", name));
        eventWriter.add(newline);
    }
    */
}