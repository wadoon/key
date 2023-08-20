package de.uka.ilkd.key.proof.runallproofs;

import java.io.Serializable;

/**
 * Data structure for RunAllProofs test results consisting of a string message and a boolean value
 * which specifies whether a test run was successful or not.
 */
public record TestResult(String message, boolean success) implements Serializable {
    private static final long serialVersionUID = 7635762713077999920L;

}
