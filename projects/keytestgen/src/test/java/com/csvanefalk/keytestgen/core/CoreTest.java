package com.csvanefalk.keytestgen.core;

import com.csvanefalk.keytestgen.KeYTestGenTest;
import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.testutils.TestEnvironment;

import java.io.IOException;

public class CoreTest extends KeYTestGenTest {

    private static TestEnvironment testEnvironment;

    public CoreTest() {
    }

    public CoreTest(String dir) throws KeYInterfaceException, IOException {
        super(dir);
    }
}
