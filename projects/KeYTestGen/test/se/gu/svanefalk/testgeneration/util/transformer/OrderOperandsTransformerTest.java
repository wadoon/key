package se.gu.svanefalk.testgeneration.util.transformer;

import java.io.IOException;

import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.util.transformers.NegationNormalFormTransformer;
import se.gu.svanefalk.testgeneration.util.transformers.OrderOperandsTransformer;

public class OrderOperandsTransformerTest extends TransformerTest {

    public OrderOperandsTransformerTest() throws KeYInterfaceException,
            IOException {
        transformer = OrderOperandsTransformer.getInstance();
    }
}
