package qantifiers;

import java.io.IOException;

import org.junit.Test;

import se.gu.svanefalk.testgeneration.KeYTestGenTest;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

public class QuantifierTest extends KeYTestGenTest {

    public QuantifierTest() throws KeYInterfaceException, IOException {
        super("own");
    }

    @Test
    public void testHandleExists() throws ProofInputException {

        IExecutionNode node = getFirstSymbolicNodeForStatement("arrAddandComp",
                "return this.arr[index1]+this.arr[index2]>20");

        System.out.println("1:" + node.getFormatedPathCondition());
        System.out.println("2:" + node.getPathCondition());
        int x = 1;
    }
}
