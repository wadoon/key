package de.uka.ilkd.key.testgeneration.core.coreinterface;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.testgeneration.core.KeYJavaClass;

/**
 * Encapsulates logic needed to construct Test Suites directly from individual
 * {@link IExecutionNode} instances.
 * 
 * @author christopher
 */
public enum NodeTestGenerator {
    INSTANCE;

    public TestSuite constructTestSuiteFromNode(IExecutionNode node) {

        KeYMediator mediator = node.getMediator();

        /*
         * Get and process the method call node
         */
        IExecutionMethodCall methodCall = getMethodCallNode(node);

        IProgramMethod method = methodCall.getProgramMethod();
        KeYJavaType parent = method.getContainerType();
        String packageDeclaration = parent.getJavaType().getFullName();
        

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
    private IExecutionMethodCall getMethodCallNode(IExecutionNode node) {

        if (node instanceof IExecutionMethodCall) {
            return (IExecutionMethodCall) node;
        } else {
            return getMethodCallNode(node.getParent());
        }
    }
}
