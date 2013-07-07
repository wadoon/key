package se.gu.svanefalk.testgeneration.core.model;

import java.io.IOException;

import se.gu.svanefalk.testgeneration.core.CoreTest;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelGenerator;

public class ModelTest extends CoreTest {

    protected  final ModelGenerator modelGenerator = ModelGenerator.getInstance();

    public ModelTest() {
    }

    public ModelTest(String dir) throws KeYInterfaceException, IOException {
        super(dir);
    }

}
