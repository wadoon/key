package se.gu.svanefalk.testgeneration.core;

import java.io.IOException;

import se.gu.svanefalk.testgeneration.KeYTestGenTest;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import testutils.TestEnvironment;

public class CoreTest extends KeYTestGenTest {

    private static TestEnvironment testEnvironment;

    public CoreTest() {
    }

    public CoreTest(String dir) throws KeYInterfaceException, IOException {
        super(dir);
    }
}
