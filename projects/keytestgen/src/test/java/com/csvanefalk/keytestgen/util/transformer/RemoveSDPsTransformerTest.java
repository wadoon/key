package com.csvanefalk.keytestgen.util.transformer;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.util.transformers.RemoveSDPsTransformer;

import java.io.IOException;

public class RemoveSDPsTransformerTest extends TransformerTest {

    public RemoveSDPsTransformerTest() throws KeYInterfaceException,
            IOException {
        transformer = RemoveSDPsTransformer.getInstance();
    }
}
