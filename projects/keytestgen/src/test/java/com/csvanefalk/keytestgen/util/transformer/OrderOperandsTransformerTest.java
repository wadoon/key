package com.csvanefalk.keytestgen.util.transformer;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.util.transformers.OrderOperandsTransformer;

import java.io.IOException;

public class OrderOperandsTransformerTest extends TransformerTest {

    public OrderOperandsTransformerTest() throws KeYInterfaceException, IOException {
        transformer = OrderOperandsTransformer.getInstance();
    }
}
