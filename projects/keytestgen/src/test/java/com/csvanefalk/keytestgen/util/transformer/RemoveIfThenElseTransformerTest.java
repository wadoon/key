package com.csvanefalk.keytestgen.util.transformer;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.util.transformers.RemoveIfThenElseTransformer;

import java.io.IOException;

public class RemoveIfThenElseTransformerTest extends TransformerTest {

    public RemoveIfThenElseTransformerTest() throws KeYInterfaceException,
            IOException {
        transformer = RemoveIfThenElseTransformer.getInstance();
    }
}
