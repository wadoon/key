package se.gu.svanefalk.testgeneration.core;

import java.io.IOException;

import junit.framework.Assert;

import org.junit.Test;

import se.gu.svanefalk.testgeneration.KeYTestGenTest;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import testutils.TestEnvironment;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;

public class CoreTest extends KeYTestGenTest {

    private static TestEnvironment testEnvironment;

    public CoreTest() {
    }

    public CoreTest(String dir) throws KeYInterfaceException, IOException {
        super(dir);
    }
}
