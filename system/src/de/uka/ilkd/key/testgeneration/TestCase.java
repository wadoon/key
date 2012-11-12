package de.uka.ilkd.key.testgeneration;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.testgeneration.model.IModel;

/**
 * Formally, a test case is a tuple (m, I, Or), where:
 * <p>
 * <ul>
 * <li><i>m</i> is the method being tested</li>
 * <li><i>I</i> is the input (Pi, Si) for the method. where Pi is a set of concrete parameter values
 * to the method (if the method accepts parameters), and Si is a state of the program holding before
 * the method starts execution.</li>
 * <li><i>Or</i> is the <i>Oracle</i> for the method being tested.</li>
 * </ul>
 * The Oracle is defined as a function Or(R, Sf) -> {pass, fail}, where:
 * <p>
 * <ul>
 * <li><i>R</i> is the return value of the function when the method finishes executing</li>
 * <li><i>Sf</i> is the final state of the program after the method finishes executing</li>
 * </ul>
 * <p>
 * Thus, less formally speaking, we can define the execution of a test case as a three-step process:
 * set up a program state to hoĺd before the method executes, execute the method, and then verify
 * that the program is in a desired state after the method finishes executing.
 * <p>
 * 
 * @author christopher
 */
public class TestCase {

    /**
     * A concrete representation of the heapstate before the test case is executed. This brings
     * together the (Pi, Si) definition of <i>I</i> as given above, in the sense that both parameter
     * values and required program state before execution will all be represented as part of the
     * same heapstate.
     */
    private IModel input;
    
    /**
     * The Oracle for the method, here represented as a postcondition (i.e. a set of logical
     * expressions defining under which conditions the Oracle would evaluate to "pass"), encoded in
     * KeYTestGens native XML format. This is necessary since KeYTestGen by itself generates no
     * methods to act as Oracles, but leave this to implementations of the {@link ITestCaseParser}
     * interface.
     */
    private String oracle;
}
