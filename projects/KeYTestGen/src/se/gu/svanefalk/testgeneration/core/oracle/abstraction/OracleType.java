package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

public final class OracleType {

    public static final OracleType INTEGER = new OracleType("int", "int");
    public static final OracleType LONG = new OracleType("long", "long");
    public static final OracleType BYTE = new OracleType("byte", "byte");
    public static final OracleType FLOAT = new OracleType("float", "float");
    public static final OracleType DOUBLE = new OracleType("double", "double");
    public static final OracleType BOOLEAN = new OracleType("boolean",
            "boolean");

    private final String fullName;
    private final String name;

    public OracleType(String name, String fullName) {
        this.name = name;
        this.fullName = fullName;
    }

    @Override
    public String toString() {
        return name;
    }
}