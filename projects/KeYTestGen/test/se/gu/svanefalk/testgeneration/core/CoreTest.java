package se.gu.svanefalk.testgeneration.core;

import java.io.IOException;

import org.junit.Test;

import junit.framework.Assert;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;

import se.gu.svanefalk.testgeneration.KeYTestGenTest;
import se.gu.svanefalk.testgeneration.SymbolicExecutionTrees;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;

public class CoreTest extends KeYTestGenTest {

    private static SymbolicExecutionTrees symbolicExecutionTrees;

    public CoreTest() throws KeYInterfaceException, IOException {
        symbolicExecutionTrees = SymbolicExecutionTrees.getInstance("/home/christopher/git/key/projects/KeYTestGen/test/se/gu/svanefalk/testgeneration/targetmodels/IntegerClass.java");
    }

    protected IExecutionStartNode getSymbolicTreeForMethod(String identifier) {
        IExecutionStartNode tree = symbolicExecutionTrees.getSymbolicTreeForNode(identifier);
        Assert.assertNotNull("Could not find tree for method: " + identifier,
                tree);
        return tree;
    }

    @Test
    public void normal() {
        Assert.assertTrue(true);
    }
}
