package de.uka.ilkd.key.testgeneration.core.coreinterface;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Encapsulates logic needed to construct Test Suites directly from individual
 * {@link IExecutionNode} instances.
 * 
 * @author christopher
 */
public enum NodeTestGenerator {
    INSTANCE;

    public TestSuite constructTestSuiteFromNode(final IExecutionNode node) {

        node.getMediator();

        /*
         * Get and process the method call node
         */
        final IExecutionMethodCall methodCall = getMethodCallNode(node);

        final IProgramMethod method = methodCall.getProgramMethod();
        final KeYJavaType parent = method.getContainerType();
        parent.getJavaType().getFullName();

        parent.getName();
        parent.getFullName();
        final PackageReference ref = parent.createPackagePrefix();
        ref.toString();
        return null;
    }

    /**
     * Given an {@link IExecutionNode} somewhere in a symbolic execution tree
     * and below the method call node, backtracks until the method call node is
     * found.
     * 
     * @param node
     *            the node
     * @return
     */
    private IExecutionMethodCall getMethodCallNode(final IExecutionNode node) {

        if (node instanceof IExecutionMethodCall) {
            return (IExecutionMethodCall) node;
        } else {
            return getMethodCallNode(node.getParent());
        }
    }
}
