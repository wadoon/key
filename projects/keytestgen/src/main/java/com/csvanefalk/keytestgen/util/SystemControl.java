package com.csvanefalk.keytestgen.util;

import com.csvanefalk.keytestgen.backend.TestGenerator;
import com.csvanefalk.keytestgen.core.CoreInterface;
import com.csvanefalk.keytestgen.core.classabstraction.KeYJavaClassFactory;
import com.csvanefalk.keytestgen.core.keyinterface.KeYInterface;

public class SystemControl {

    public static void disposeSystem() {

        TestGenerator.__DEBUG_DISPOSE();
        //ModelGenerator.__DEBUG_DISPOSE();
        KeYInterface.__DEBUG_DISPOSE();
        KeYJavaClassFactory.__DEBUG_DISPOSE();
        CoreInterface.__DEBUG_DISPOSE();
    }
}
