package se.gu.svanefalk.testgeneration.core;

import java.io.IOException;

import junit.framework.Assert;

import org.junit.Test;

import se.gu.svanefalk.testgeneration.KeYTestGenTest;
import se.gu.svanefalk.testgeneration.TestEnvironment;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;

public class CoreTest extends KeYTestGenTest {

    private static TestEnvironment testEnvironment;

    public CoreTest() throws KeYInterfaceException, IOException {
        testEnvironment = TestEnvironment.getInstance("/home/christopher/git/key/projects/KeYTestGen/test/se/gu/svanefalk/testgeneration/targetmodels/IntegerClass.java");
    }

    protected IExecutionStartNode getSymbolicTreeForMethod(String identifier) {
        IExecutionStartNode tree = testEnvironment.getSymbolicTreeForNode(identifier);
        Assert.assertNotNull("Could not find tree for method: " + identifier,
                tree);
        return tree;
    }

    @Test
    public void normal() {
        Assert.assertTrue(true);
    }
}
