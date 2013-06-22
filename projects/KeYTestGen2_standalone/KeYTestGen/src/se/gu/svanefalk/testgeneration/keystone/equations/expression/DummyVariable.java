package se.gu.svanefalk.testgeneration.keystone.equations.expression;

public class DummyVariable extends Variable {

    private static int dummyVariableIndex = 1;

    private static String dummyVariablePrefix = "keystone_dummyvariable";

    public static DummyVariable createDummyVariable() {
        return new DummyVariable(DummyVariable.dummyVariablePrefix
                + DummyVariable.dummyVariableIndex++);
    }

    private DummyVariable(final String name) {
        super(name);
        // TODO Auto-generated constructor stub
    }
}
