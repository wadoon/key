package de.uka.ilkd.key.testgeneration.visitors;

import javax.xml.stream.XMLStreamException;

import de.uka.ilkd.key.testgeneration.TestCaseGeneratorException;

public class XMLVisitorException
        extends TestCaseGeneratorException {

    private static final long serialVersionUID = -286893052052896384L;

    public XMLVisitorException(String message) {

        super(message);
    }

    public XMLVisitorException(String message, Throwable cause) {
        super(message, cause);
        
    }
}
