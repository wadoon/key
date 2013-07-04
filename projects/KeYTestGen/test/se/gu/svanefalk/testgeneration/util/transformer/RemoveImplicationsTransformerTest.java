package se.gu.svanefalk.testgeneration.util.transformer;

import java.io.IOException;

import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.util.transformers.RemoveImplicationsTransformer;

public class RemoveImplicationsTransformerTest extends TransformerTest {

    public RemoveImplicationsTransformerTest() throws KeYInterfaceException,
            IOException {
        transformer = RemoveImplicationsTransformer.getInstance();
    }
}
