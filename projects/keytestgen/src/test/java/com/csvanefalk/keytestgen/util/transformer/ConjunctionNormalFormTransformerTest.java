package com.csvanefalk.keytestgen.util.transformer;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.util.transformers.ConjunctionNormalFormTransformer;

import java.io.IOException;

public class ConjunctionNormalFormTransformerTest extends TransformerTest {

    public ConjunctionNormalFormTransformerTest() throws KeYInterfaceException, IOException {
        transformer = ConjunctionNormalFormTransformer.getInstance();
    }
}
