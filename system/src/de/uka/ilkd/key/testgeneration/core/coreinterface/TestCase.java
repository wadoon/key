package de.uka.ilkd.key.testgeneration.core.coreinterface;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.testgeneration.core.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.core.model.implementation.Model;

/**
 * Formally, a test case is a tuple (m, I, Or), where:
 * <p>
 * <ul>
 * <li><i>m</i> is the method being tested</li>
 * <li><i>I</i> is the input (Pi, Si) for the method. where Pi is a set of
 * concrete parameter values to the method (if the method accepts parameters),
 * and Si is a state of the program holding before the method starts execution.</li>
 * <li><i>Or</i> is the <i>Oracle</i> for the method being tested.</li>
 * </ul>
 * The Oracle is defined as a function Or(R, Sf) -> {pass, fail}, where:
 * <p>
 * <ul>
 * <li><i>R</i> is the return value of the function when the method finishes
 * executing</li>
 * <li><i>Sf</i> is the final state of the program after the method finishes
 * executing</li>
 * </ul>
 * <p>
 * Thus, less formally speaking, we can define the execution of a test case as a
 * three-step process: set up a program state to hoĺd before the method
 * executes, execute the method, and then verify that the program is in a
 * desired state after the method finishes executing.
 * <p>
 * 
 * @author christopher
 */
public class TestCase implements Comparable<TestCase> {

    /**
     * DEBUG: the execution node associated with this test case.
     */
    private IExecutionNode node;

    /**
     * The method for which the test case is being generated.
     */
    private final KeYJavaMethod method;

    /**
     * A concrete representation of the heapstate before the test case is
     * executed. This brings together the (Pi, Si) definition of <i>I</i> as
     * given above, in the sense that both parameter values and required program
     * state before execution will all be represented as part of the same
     * heapstate.
     */
    private final Model model;

    /**
     * The Oracle for the method, here represented as a postcondition (i.e. a
     * set of logical expressions defining under which conditions the Oracle
     * would evaluate to "pass"), here represented in its native {@link Term}
     * format.
     */
    private final Term oracle;

    public TestCase(final KeYJavaMethod method, final Model model,
            final Term oracle) {

        this.method = method;
        this.model = model;
        this.oracle = oracle;
    }

    @Override
    public int compareTo(final TestCase o) {

        final String ownName = method.getProgramMethod().getName();
        final String otherName = o.getMethod().getProgramMethod().getName();

        return ownName.compareTo(otherName);
    }

    /**
     * Retrieve the {@link KeYJavaMethod} this testcase belongs to.
     * 
     * @return
     */
    public KeYJavaMethod getMethod() {

        return method;
    }

    /**
     * @return the name of the method handled by this tescase
     */
    public String getMethodName() {
        return method.getProgramMethod().getName();
    }

    /**
     * Retrieve the {@link IModel} instance for this test case.
     * 
     * @return
     */
    public Model getModel() {

        return model;
    }

    /**
     * @return the node
     */
    public IExecutionNode getNode() {
        return node;
    }

    /**
     * Retrieve the oracle for the test case.
     * 
     * @return
     */
    public Term getOracle() {

        return oracle;
    }

    /**
     * @param node
     *            the node to set
     */
    public void setNode(final IExecutionNode node) {
        this.node = node;
    }

}