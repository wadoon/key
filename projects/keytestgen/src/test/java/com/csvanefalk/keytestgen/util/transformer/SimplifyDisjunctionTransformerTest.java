package com.csvanefalk.keytestgen.util.transformer;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.util.transformers.SimplifyDisjunctionTransformer;

import java.io.IOException;

public class SimplifyDisjunctionTransformerTest extends TransformerTest {

    public SimplifyDisjunctionTransformerTest() throws KeYInterfaceException, IOException {
        transformer = SimplifyDisjunctionTransformer.getInstance();
    }
}
