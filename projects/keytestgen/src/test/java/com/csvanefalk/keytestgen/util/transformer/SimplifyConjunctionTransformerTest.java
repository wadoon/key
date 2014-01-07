package com.csvanefalk.keytestgen.util.transformer;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.util.transformers.SimplifyConjunctionTransformer;

import java.io.IOException;

public class SimplifyConjunctionTransformerTest extends TransformerTest {

    public SimplifyConjunctionTransformerTest() throws KeYInterfaceException, IOException {
        transformer = SimplifyConjunctionTransformer.getInstance();
    }
}
