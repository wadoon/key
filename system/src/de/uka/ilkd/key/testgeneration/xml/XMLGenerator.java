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
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaClass;
import de.uka.ilkd.key.testgeneration.model.IModel;

/**
 * Encapsulates the functionality needed to translate a model into a standard XML representation.
 * The associated schema is TestCase.xsd, with related schema JavaClass.xsd.
 * 
 * @author christopher
 */
public enum XMLGenerator {
    INSTANCE;
    

}