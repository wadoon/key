package com.csvanefalk.keytestgen.util.transformer;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.util.transformers.RemoveObserverFunctionsTransformer;

import java.io.IOException;

public class RemoveObserverFunctionsTransformerTest extends TransformerTest {

    public RemoveObserverFunctionsTransformerTest()
            throws KeYInterfaceException, IOException {
        transformer = RemoveObserverFunctionsTransformer.getInstance();
    }
}
