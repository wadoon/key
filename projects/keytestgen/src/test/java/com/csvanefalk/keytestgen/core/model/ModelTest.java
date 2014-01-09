package com.csvanefalk.keytestgen.core.model;

import com.csvanefalk.keytestgen.core.CoreTest;
import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.core.model.implementation.ModelGenerator;

import java.io.IOException;

public class ModelTest extends CoreTest {

    protected final ModelGenerator modelGenerator = ModelGenerator.getInstance();

    public ModelTest() {
    }

    public ModelTest(String dir) throws KeYInterfaceException, IOException {
        super(dir);
    }

    public ModelTest(String dir,
                     boolean loadSubDirectories,
                     String... files) throws KeYInterfaceException, IOException {
        super(dir, loadSubDirectories, files);
    }

}
