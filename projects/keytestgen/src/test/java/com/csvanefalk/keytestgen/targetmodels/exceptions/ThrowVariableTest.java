package com.csvanefalk.keytestgen.targetmodels.exceptions;

public class ThrowVariableTest {
    public void main(int x) {
        IllegalArgumentException e = new IllegalArgumentException();
        throw e;
    }
}
