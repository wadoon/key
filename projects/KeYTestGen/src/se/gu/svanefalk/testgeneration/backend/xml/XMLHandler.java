package se.gu.svanefalk.testgeneration.backend.xml;

import java.util.LinkedList;
import java.util.List;

/**
 * Contains various constants and utility methods related to handling and
 * generating XML in KeYTestGen2.
 * 
 * @author christopher
 */
public abstract class XMLHandler {

    /**
     * Root tag name for fields
     */
    protected static final String FIELD_ROOT = "field";
    /**
     * Root tag name for heap object identifiers.
     */
    protected static final String IDENTIFIER_ROOT = "identifier";

    /**
     * Root tag name for object instances
     */
    protected static final String INSTANCE_ROOT = "instance";

    /**
     * Root tag name for object instance sets
     */
    protected static final String INSTANCES_ROOT = "instances";

    /**
     * Root tag name for methods.
     */
    protected static final String METHOD_ROOT = "method";

    /**
     * Root tag name for names (either for variables or methods).
     */
    protected static final String NAME_ROOT = "name";

    /**
     * Root tag for oracles
     */
    protected static final String ORACLE_ROOT = "oracle";

    /**
     * Root tag name for parameters.
     */
    protected static final String PARAMETERS_ROOT = "parameters";

    protected static final List<String> primitiveTypes = new LinkedList<String>();

    /**
     * Root tag name for the base class
     */
    protected static final String SELF_ROOT = "self";

    /**
     * Root tag name for a test case.
     */
    protected static final String TESTCASE_ROOT = "testcase";

    /**
     * Root tag name for test fixtures.
     */
    protected static final String TESTFIXTURE_ROOT = "fixture";

    /**
     * Root tag name for test suites.
     */
    protected static final String TESTSUITE_ROOT = "testsuite";

    /**
     * Root tag name for types
     */
    protected static final String TYPE_ROOT = "type";

    /**
     * Root tag name for values
     */
    protected static final String VALUE_ROOT = "value";

    /**
     * Root tag name for variables
     */
    protected static final String VARIABLE_ROOT = "variable";

    /**
     * Root tag name for variables
     */
    protected static final String VARIABLES_ROOT = "variables";

    static {
        XMLHandler.primitiveTypes.add("byte");
        XMLHandler.primitiveTypes.add("int");
        XMLHandler.primitiveTypes.add("long");
        XMLHandler.primitiveTypes.add("boolean");
    }

}
