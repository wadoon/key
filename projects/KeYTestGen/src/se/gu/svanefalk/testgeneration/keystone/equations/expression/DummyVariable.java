package se.gu.svanefalk.testgeneration.keystone.equations.expression;

public class DummyVariable extends Variable {

    private static String dummyVariablePrefix = "keystone_dummyvariable";

    private static int dummyVariableIndex = 1;

    private DummyVariable(String name) {
        super(name);
        // TODO Auto-generated constructor stub
    }

    public static Variable createDummyVariable() {
        return new DummyVariable(dummyVariablePrefix + dummyVariableIndex++);
    }
}
