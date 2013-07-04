package se.gu.svanefalk.testgeneration.util.transformer;

import java.io.IOException;

import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.util.transformers.RemoveObserverFunctionsTransformer;

public class RemoveObserverFunctionsTransformerTest extends TransformerTest {

    public RemoveObserverFunctionsTransformerTest()
            throws KeYInterfaceException, IOException {
        transformer = RemoveObserverFunctionsTransformer.getInstance();
    }
}
