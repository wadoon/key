package com.csvanefalk.keytestgen.util.transformer;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.util.transformers.NegationNormalFormTransformer;

import java.io.IOException;

public class NegationNormalFormTransformerTest extends TransformerTest {

    public NegationNormalFormTransformerTest() throws KeYInterfaceException,
            IOException {
        transformer = NegationNormalFormTransformer.getInstance();
    }
}
