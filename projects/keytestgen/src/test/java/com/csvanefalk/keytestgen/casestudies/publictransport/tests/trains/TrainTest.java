package com.csvanefalk.keytestgen.casestudies.publictransport.tests.trains;

import com.csvanefalk.keytestgen.KeYTestGenTest;
import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.targetmodels.publictransport.trains.train.Train;
import org.junit.Assert;
import org.junit.Test;

import java.io.IOException;

/**
 * Test case generation tests for the {@link Train} class.
 *
 * @author christopher
 */
public class TrainTest extends KeYTestGenTest {

    public TrainTest() throws KeYInterfaceException, IOException {
        super("publictransport/trains");
    }

    @Test
    public void testStuff() {
        Assert.assertTrue(true);
    }
}
