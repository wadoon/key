package se.gu.svanefalk.testgeneration.util.transformer;

import java.io.IOException;

import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.util.transformers.ConjunctionNormalFormTransformer;
import se.gu.svanefalk.testgeneration.util.transformers.NegationNormalFormTransformer;

public class ConjunctionNormalFormTransformerTest extends TransformerTest {

    public ConjunctionNormalFormTransformerTest() throws KeYInterfaceException,
            IOException {
        transformer = ConjunctionNormalFormTransformer.getInstance();
    }
}
