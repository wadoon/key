package com.csvanefalk.keytestgen.backend;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Implementors of this interface represent test case generators which are
 * capable of generating test cases for single {@link IExecutionNode} instances.
 *
 * @author christopher
 */
public interface INodeTestCaseGenerator {

    /**
     * Generates a test case for a single {@link IExecutionNode} instance,
     * corresponding to a single statement in a single method.
     *
     * @param targetNode the target program node
     * @param services   {@link Services} instance for the execution node
     * @return the entire test suite as a String.
     * @throws TestGeneratorException in the event that something went wrong.
     */
    public String generateTestCase(final IExecutionNode targetNode,
                                   final Services services) throws TestGeneratorException;

}
