package com.csvanefalk.keytestgen.keystone.equations;

import javax.naming.OperationNotSupportedException;

public interface IComparator {

    boolean evaluate() throws OperationNotSupportedException;
}