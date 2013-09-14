package casestudies.publictransport.tests.trains;

import java.io.IOException;

import org.junit.Assert;
import org.junit.Test;

import se.gu.svanefalk.testgeneration.KeYTestGenTest;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import targetmodels.publictransport.trains.train.Train;

/**
 * Test case generation tests for the {@link Train} class.
 * 
 * @author christopher
 * 
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
