package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

/**
 * Represents the types of elements in an Oracle.
 * 
 * @author christopher
 * 
 */
public final class OracleType {

    /*
     * The primitive Java types.
     */
    public static final OracleType INTEGER = new OracleType("int", "int");
    public static final OracleType LONG = new OracleType("long", "long");
    public static final OracleType BYTE = new OracleType("byte", "byte");
    public static final OracleType FLOAT = new OracleType("float", "float");
    public static final OracleType DOUBLE = new OracleType("double", "double");
    public static final OracleType BOOLEAN = new OracleType("boolean",
            "boolean");

    /**
     * The full name of the type (i.e. including the package declaration, if
     * any).
     */
    private final String fullName;

    /**
     * The name of the type.
     */
    private final String name;

    /**
     * Construct a new type.
     * 
     * @param name
     *            the name of the type
     * @param fullName
     *            the name of the type, including its package declaration
     */
    public OracleType(String name, String fullName) {
        this.name = name;
        this.fullName = fullName;
    }

    @Override
    public String toString() {
        return name;
    }
}