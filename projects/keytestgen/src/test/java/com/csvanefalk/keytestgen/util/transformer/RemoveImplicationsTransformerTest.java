package com.csvanefalk.keytestgen.util.transformer;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.util.transformers.RemoveImplicationsTransformer;

import java.io.IOException;

public class RemoveImplicationsTransformerTest extends TransformerTest {

    public RemoveImplicationsTransformerTest() throws KeYInterfaceException,
            IOException {
        transformer = RemoveImplicationsTransformer.getInstance();
    }
}
