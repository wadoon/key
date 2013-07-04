package se.gu.svanefalk.testgeneration.util.transformer;

import java.io.IOException;

import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.util.transformers.RemoveIfThenElseTransformer;

public class RemoveIfThenElseTransformerTest extends TransformerTest {

    public RemoveIfThenElseTransformerTest() throws KeYInterfaceException,
            IOException {
        transformer =RemoveIfThenElseTransformer.getInstance();
    }
}
