package se.gu.svanefalk.testgeneration.util;

import se.gu.svanefalk.testgeneration.backend.TestGenerator;
import se.gu.svanefalk.testgeneration.core.CoreInterface;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClassFactory;
import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterface;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelGenerator;

public class SystemControl {

    public static void disposeSystem() {

        TestGenerator.__DEBUG_DISPOSE();
        ModelGenerator.__DEBUG_DISPOSE();
        KeYInterface.__DEBUG_DISPOSE();
        KeYJavaClassFactory.__DEBUG_DISPOSE();
        CoreInterface.__DEBUG_DISPOSE();
    }
}
