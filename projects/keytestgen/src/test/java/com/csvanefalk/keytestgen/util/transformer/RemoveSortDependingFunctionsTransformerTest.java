package com.csvanefalk.keytestgen.util.transformer;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.util.transformers.RemoveSortDependingFunctionsTransformer;

import java.io.IOException;

public class RemoveSortDependingFunctionsTransformerTest extends TransformerTest {

    public RemoveSortDependingFunctionsTransformerTest() throws KeYInterfaceException, IOException {
        transformer = RemoveSortDependingFunctionsTransformer.getInstance();
    }
}
