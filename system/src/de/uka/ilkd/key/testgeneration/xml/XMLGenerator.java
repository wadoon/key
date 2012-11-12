package de.uka.ilkd.key.testgeneration.xml;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.text.ParseException;

import javax.xml.stream.XMLEventFactory;
import javax.xml.stream.XMLEventWriter;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.events.XMLEvent;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.testgeneration.model.IModel;

/**
 * Encapsulates the functionality needed to translate a model into a standard XML representation.
 * The associated schema is TestCase.xsd, with related schema JavaClass.xsd.
 * 
 * @author christopher
 */
public enum XMLGenerator {
    INSTANCE;
    
    public String generateXMLTestSuite(IModel model, IExecutionStartNode symbolicTreeRoot) {
        
        /*
         * Generate XML for the preconditions
         */
        
        /*
         * Generate XML for the postconditions
         */
        return null;
    }
    
}