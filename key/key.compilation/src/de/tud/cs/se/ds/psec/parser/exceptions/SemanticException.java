package de.tud.cs.se.ds.psec.parser.exceptions;

/**
 * A semantic exception occurred during parsing the translation taclet
 * definitions.
 *
 * @author Dominic Scheurer
 */
@SuppressWarnings("serial")
public class SemanticException extends RuntimeException {

    public SemanticException(String message) {
        super(message);
    }
}
