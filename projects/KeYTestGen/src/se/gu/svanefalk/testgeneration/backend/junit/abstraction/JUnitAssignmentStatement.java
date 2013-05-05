package se.gu.svanefalk.testgeneration.backend.junit.abstraction;

/**
 * Instances of this class represent field assignment assertions in a JUnit test
 * class.
 * <p>
 * Given some Object o and field x of o, such a statments assigns a
 * (type-coherent w.r.t. x) value v to x:
 * 
 * <pre>
 * <code>o.x = v</code>
 * </pre>
 * 
 * This class defines only the data needed to construct such a statement, it
 * does not define how the actual field access takes place at the source code
 * level.
 * 
 * @author christopher
 * 
 */
public class JUnitAssignmentStatement {

    /**
     * The identifier name of the field.
     */
    private final String fieldName;

    /**
     * The identifier name (for a reference type), or raw value (for a primitive
     * type) of the value being assigned to the field.
     */
    private final String fieldValue;

    /**
     * The identifier name of the object which the field belongs to.
     */
    private final String objectName;

    public JUnitAssignmentStatement(final String objectName,
            final String fieldName, final String fieldValue) {
        this.objectName = objectName;
        this.fieldName = fieldName;
        this.fieldValue = fieldValue;
    }

    /**
     * @return the fieldName
     */
    public String getFieldName() {
        return fieldName;
    }

    /**
     * @return the fieldValue
     */
    public String getFieldValue() {
        return fieldValue;
    }

    /**
     * @return the objectName
     */
    public String getObjectName() {
        return objectName;
    }
}