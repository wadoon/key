package com.csvanefalk.keytestgen.qantifiers;

import com.csvanefalk.keytestgen.KeYTestGenTest;
import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import org.junit.Test;

import java.io.IOException;

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
