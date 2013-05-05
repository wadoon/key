package se.gu.svanefalk.testgeneration.keystone.equations;

import javax.naming.OperationNotSupportedException;

public interface IComparator {

    boolean evaluate() throws OperationNotSupportedException;
}