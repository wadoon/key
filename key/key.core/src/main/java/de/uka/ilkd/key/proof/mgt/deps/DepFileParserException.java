package de.uka.ilkd.key.proof.mgt.deps;

public class DepFileParserException extends Exception {
    public DepFileParserException(String message) {
        super("Cannot parse Dependency File: " + message);
    }
}
