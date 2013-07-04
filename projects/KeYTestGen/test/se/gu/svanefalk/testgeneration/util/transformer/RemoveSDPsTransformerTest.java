package se.gu.svanefalk.testgeneration.util.transformer;

import java.io.IOException;

import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.util.transformers.RemoveSDPsTransformer;

public class RemoveSDPsTransformerTest extends TransformerTest {

    public RemoveSDPsTransformerTest() throws KeYInterfaceException,
            IOException {
        transformer = RemoveSDPsTransformer.getInstance();
    }
}
