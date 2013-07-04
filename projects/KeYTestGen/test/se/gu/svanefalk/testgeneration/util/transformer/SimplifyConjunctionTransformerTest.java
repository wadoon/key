package se.gu.svanefalk.testgeneration.util.transformer;

import java.io.IOException;

import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.util.transformers.SimplifyConjunctionTransformer;

public class SimplifyConjunctionTransformerTest extends TransformerTest {

    public SimplifyConjunctionTransformerTest() throws KeYInterfaceException,
            IOException {
        transformer = SimplifyConjunctionTransformer.getInstance();
    }
}
