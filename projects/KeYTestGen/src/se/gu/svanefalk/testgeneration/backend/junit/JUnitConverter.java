package se.gu.svanefalk.testgeneration.backend.junit;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import se.gu.svanefalk.testgeneration.backend.AbstractJavaSourceGenerator;
import se.gu.svanefalk.testgeneration.backend.IFrameworkConverter;
import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClass;
import se.gu.svanefalk.testgeneration.core.model.implementation.Model;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelInstance;
import se.gu.svanefalk.testgeneration.core.model.implementation.ModelVariable;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleAssertion;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleComparator;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleConstraint;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleExpression;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleLiteral;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleMethodInvocation;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleOperator;
import se.gu.svanefalk.testgeneration.core.testsuiteabstraction.TestCase;
import se.gu.svanefalk.testgeneration.core.testsuiteabstraction.TestSuite;
import de.uka.ilkd.key.logic.op.IProgramVariable;

/**
 * This singleton provides the functionality needed to produce test suites for
 * the JUnit framework.
 * 
 * @author christopher
 * 
 */
public class JUnitConverter extends AbstractJavaSourceGenerator implements
        IFrameworkConverter {

    /**
     * Worker which services invocations of
     * {@link JUnitConverter#convertToJUnit(List)}.
     * 
     * @author christopher
     * 
     */
    private static class JUnitGeneratorWorker extends
            AbstractJavaSourceGenerator {

        /**
         * The name of the container for the result value (if any) resulting
         * from the invocation of a method being tested. This value is used in
         * the assertion process, and must not conflict with the names of any
         * parameter values.
         */
        private static final String EXECUTION_RESULT = "result";

        /**
         * The name of the root variable (i.e. the variable pointing to the
         * instane of the object that has the methods to be tested).
         */
        private static final String SELF = "self";

        /**
         * The name of the class for which the test suite is being generated.
         * Kept for the purpose of naming and type declaration.
         */
        private String className = "X";

        /**
         * Used to differentiate between the names of test cases.
         */
        private int ID = 0;

        /**
         * Imports to be included in this test class
         */
        private final HashSet<String> imports = new HashSet<String>();

        /**
         * Given a set of {@link TestCase} instances, this method will extract
         * put all {@link ModelInstance} declared in the model of each testcase
         * into a single list.
         * 
         * @param testCases
         *            the test cases
         * @return a list of all instances declared in all test cases models
         */
        private List<ModelInstance> collectInstances(
                final List<TestCase> testCases) {

            final List<ModelInstance> instances = new LinkedList<ModelInstance>();
            for (final TestCase testCase : testCases) {
                final List<ModelInstance> collectedInstances = extractInstancesFromModel(testCase.getModel());
                instances.addAll(collectedInstances);
            }

            return instances;
        }

        /**
         * Sets up the fixture repository for a given test class. This
         * repository will contain the object instances needed for the test
         * cases to run.
         * 
         * @param testCases
         *            the test cases for the test class.
         */
        private void createFixtureRepository(final List<TestCase> testCases) {

            /*
             * Safeguard from first invocation errors.
             */
            if (testCases.isEmpty()) {
                return;
            }

            /*
             * Write the HashMap for holding the object instances.
             */
            // this.writeObjectInstanceMap();

            /*
             * Write the method for retrieving the actual test instances.
             */
            // this.writeGetObjectInstanceMethod();

            /*
             * Write the method for setting fields of objects.
             */
            writeSetFieldMethod();

            /*
             * Write the method for getting fields of objects.
             */
            writeGetFieldMethod();

            /*
             * Write the main init method for creating the repository of Object
             * instances.
             */
            // this.writeCreateInstanceRepositoryMethod(testCases);
        }

        /**
         * Given a {@link Model}, this method will extract all instances of
         * {@link ModelInstance} from it.
         * 
         * @param model
         * @return
         */
        private List<ModelInstance> extractInstancesFromModel(final Model model) {

            final List<ModelInstance> instances = new LinkedList<ModelInstance>();
            for (final ModelVariable variable : model.getVariables()) {
                if (variable.getValue() instanceof ModelInstance) {
                    instances.add((ModelInstance) variable.getValue());
                }
            }
            return instances;
        }

        @Override
        protected String getCurrentOutput() {

            final StringBuilder builder = new StringBuilder();

            /*
             * Write the package declaration.
             */
            builder.append("package ");
            builder.append(className);
            builder.append("TestClass;\n\n");

            /*
             * Write the general imports (JUnit libs etc)
             */
            builder.append("import ");
            builder.append("org.junit.*");
            builder.append(";\n");

            builder.append("import ");
            builder.append("java.lang.reflect.*");
            builder.append(";\n");

            builder.append("import ");
            builder.append("java.util.*");
            builder.append(";\n");

            /*
             * Write the specific imports.
             */
            for (final String importt : imports) {
                builder.append("import ");
                builder.append(importt);
                builder.append(";\n");
            }
            builder.append(AbstractJavaSourceGenerator.NEWLINE);
            builder.append(super.getCurrentOutput());

            return builder.toString();
        }

        /**
         * Services invocations of
         * {@link JUnitConverter#generateJUnitSources(KeYJavaClass, List)}
         * 
         * @param klass
         *            the class for which we are generating test cases
         * @param testCases
         *            the test cases to generate
         * @return a JUnit source file in String format
         * @throws JUnitConverterException
         */
        public String serviceConvert(final TestSuite testSuite)
                throws JUnitConverterException {

            final List<TestCase> testCases = testSuite.getTestCases();
            final KeYJavaClass klass = testSuite.getJavaClass();
            testSuite.getMethod();

            /*
             * Collect the import assertions.
             */
            final List<ModelInstance> instances = collectInstances(testCases);
            for (final ModelInstance instance : instances) {
                final String toImport = instance.getType();
                imports.add(toImport);
            }

            /*
             * Get the name of the class being tested.
             */
            className = klass.getName();

            final String methodName = testCases.get(0).getMethodName();

            /*
             * Print the new class header
             */
            writeClassHeader(null, "public", "", "Test_" + klass.getName()
                    + "_" + methodName);

            /*
             * Create one test method for each test case.
             */
            for (final TestCase testCase : testCases) {

                writeTestMethod(testCase);
            }

            /*
             * Create the fixutre repository for this class
             */
            createFixtureRepository(testCases);

            /*
             * Close the class body.
             */
            writeClosingBrace();

            return getCurrentOutput();
        }

        /**
         * Writes the getField method.
         */
        private void writeGetFieldMethod() {

            writeComment("Gets the field of a given object", true);
            writeMethodHeader(null, "private", new String[] { "<T>" }, "T",
                    "getFieldValue", new String[] { "Object instance",
                            "String fieldName" }, new String[] {
                            "NoSuchFieldException", "SecurityException",
                            "IllegalArgumentException",
                            "IllegalAccessException" });

            writeIndentedLine("Field field = instance.getClass().getDeclaredField(fieldName);");
            writeNewLine();

            writeIndentedLine("field.setAccessible(true);");
            writeNewLine();

            writeIndentedLine("return (T)field.get(instance);");
            writeNewLine();

            writeClosingBrace();
        }

        /**
         * Writes the logic needed to invoke the method under test (MUT) for a
         * given testcase. If the MUT is of non-void type, this logic will
         * include a temporary variable for storing the result.
         * 
         * @param testCase
         */
        private void writeMethodInvocation(final TestCase testCase) {

            final String returnType = testCase.getMethod().getReturnType();
            String methodInvocation = "";
            if (!returnType.equals("void")) {
                methodInvocation += returnType + " "
                        + JUnitGeneratorWorker.EXECUTION_RESULT + " = ";
            }

            methodInvocation += JUnitGeneratorWorker.SELF + "."
                    + testCase.getMethodName() + "(";
            final List<IProgramVariable> parameters = testCase.getMethod().getParameters();

            for (int i = 0; i < parameters.size(); i++) {
                final String parameterName = parameters.get(i).name().toString();
                methodInvocation += parameterName;
                if (i != (parameters.size() - 1)) {
                    methodInvocation += ",";
                }
            }
            methodInvocation += ");";
            writeIndentedLine(methodInvocation);
            writeNewLine();
        }

        /**
         * Writes the test oracle for a given method.
         * 
         * @param testCase
         */
        private void writeOracle(final TestCase testCase) {

            writeComment("Test oracle", false);

            final OracleConstraint constraint = testCase.getOracle().getConstraints();
            for (final OracleAssertion assertion : constraint.getAssertions()) {
                writeOracleAssertion(assertion);
            }
        }

        private void writeOracleAssertion(final OracleAssertion assertion) {

            /*
             * Write opening of assertion statement
             */
            writeIndentedLine("Assert.assertTrue(");
            writeNewLine();
            increaseIndentation();
            indent();

            /*
             * Write body
             */
            final Iterator<OracleExpression> iterator = assertion.getExpressions().iterator();
            OracleExpression expression = null;
            while (iterator.hasNext()) {
                expression = iterator.next();
                writeOracleExpression(expression);

                if (iterator.hasNext()) {
                    writeUnindentedLine(" ||");
                    writeNewLine();
                    indent();
                }
            }

            /*
             * Close assertion statement
             */
            writeNewLine();
            decreaseIndentation();
            writeIndentedLine(");");
            writeNewLine();
            writeNewLine();
        }

        private void writeOracleComparator(final OracleComparator comparator) {
            writeOracleExpression(comparator.getFirstOperand());
            writeUnindentedLine(" " + comparator.getComparatorType() + " ");
            writeOracleExpression(comparator.getSecondOperand());
        }

        private void writeOracleExpression(final OracleExpression expression) {

            if (expression instanceof OracleComparator) {
                final OracleComparator comparator = (OracleComparator) expression;
                writeOracleComparator(comparator);
            }

            else if (expression instanceof OracleOperator) {
                final OracleOperator operator = (OracleOperator) expression;
                writeOracleOperator(operator);
            }

            else if (expression instanceof OracleLiteral) {
                final OracleLiteral literal = (OracleLiteral) expression;
                writeOracleLiteral(literal);
            }

            else if (expression instanceof OracleMethodInvocation) {
                final OracleMethodInvocation methodInvocation = (OracleMethodInvocation) expression;
                writeOracleMethodInvocation(methodInvocation);
            }
        }

        private void writeOracleLiteral(final OracleLiteral literal) {
            writeUnindentedLine(literal.getIdentifier());
        }

        private void writeOracleMethodInvocation(
                final OracleMethodInvocation methodInvocation) {
            // TODO
        }

        private void writeOracleOperator(final OracleOperator operator) {
            writeOracleExpression(operator.getFirstOperand());
            writeUnindentedLine(" " + operator.getOperation() + " ");
            writeOracleExpression(operator.getSecondOperand());
        }

        /**
         * Writes the setField method.
         */
        private void writeSetFieldMethod() {

            writeComment("Sets a field of some object to a given value", true);
            writeMethodHeader(null, "private", null, "void", "setFieldValue",
                    new String[] { "Object instance", "String fieldName",
                            "Object value" }, new String[] {
                            "NoSuchFieldException", "SecurityException",
                            "IllegalArgumentException",
                            "IllegalAccessException" });

            writeIndentedLine("Field field = instance.getClass().getDeclaredField(fieldName);");
            writeNewLine();

            writeIndentedLine("field.setAccessible(true);");
            writeNewLine();

            writeIndentedLine("field.set(instance, value );");
            writeNewLine();

            writeClosingBrace();
        }

        /**
         * Writes the fixture portion of a JUnit test method. Primarily, this
         * involves declaring and instantiating variables and parameter values.
         * Only variables declared on the top level are considered here.
         * 
         * @param model
         *            {@link Model} instance representing the fixture
         */
        private void writeTestFixture(final TestCase testCase) {

            /*
             * Begin with declaring all the instance variables needed for the
             * current test case.
             */
            writeComment("Create the values needed for this test case.", false);
            for (final ModelVariable variable : testCase.getModel().getVariables()) {

                if (!variable.isParameter()) {

                    /*
                     * Declares and instantiates a reference typed instance.
                     */
                    if (variable.getValue() instanceof ModelInstance) {
                        writeIndentedLine(variable.getTypeName() + " "
                                + variable.getIdentifier() + " = " + "new"
                                + " " + variable.getTypeName() + "();");
                    }

                    /*
                     * Declares and instantiates a primitive typed instance, but
                     * only if they are parameters (other primitive values will
                     * be configured as part of the classes they are fields of).
                     */
                    else {
                        writeIndentedLine(variable.getTypeName() + " "
                                + variable.getIdentifier() + " = "
                                + variable.getValue() + ";");
                    }

                    writeNewLine();
                }
            }

            /*
             * Next, create the method parameters (we do this separately for the
             * sake of clarity).
             */
            writeComment(
                    "Create the parameter instances to be passed to the method under test.",
                    false);

            for (final ModelVariable variable : testCase.getModel().getVariables()) {

                if (variable.isParameter()) {

                    /*
                     * Declares and instantiates a reference typed instance.
                     */
                    if (variable.getValue() instanceof ModelInstance) {
                        writeIndentedLine(variable.getTypeName() + " "
                                + variable.getIdentifier() + " = " + "new"
                                + " " + variable.getTypeName() + "();");
                    }

                    /*
                     * Declares and instantiates a primitive typed instance, but
                     * only if they are parameters (other primitive values will
                     * be configured as part of the classes they are fields of).
                     */
                    else {
                        writeIndentedLine(variable.getTypeName() + " "
                                + variable.getIdentifier() + " = "
                                + variable.getValue() + ";");
                    }
                    writeNewLine();
                }
            }

            /*
             * Next, configure the needed instances properly.
             */
            for (final ModelVariable variable : testCase.getModel().getVariables()) {

                /*
                 * Again, deal only with those variables which are not
                 * parameters.
                 */
                if (!variable.isParameter()) {

                    final Object value = variable.getValue();

                    if (value instanceof ModelInstance) {

                        writeComment(
                                "Configuring variable: "
                                        + variable.getIdentifier(), false);

                        final String variableIdentifier = variable.getIdentifier();
                        final ModelInstance instance = (ModelInstance) value;

                        for (final ModelVariable field : instance.getFields()) {

                            String fieldValueIdentifier = "";
                            if (field.getValue() instanceof ModelInstance) {
                                fieldValueIdentifier = field.getIdentifier();
                            } else {
                                final Object fieldValue = field.getValue();
                                fieldValueIdentifier = fieldValue.toString();
                            }

                            writeIndentedLine("setFieldValue("
                                    + variableIdentifier + "," + "\""
                                    + field.getVariableName() + "\"" + ","
                                    + fieldValueIdentifier + ");");

                            writeNewLine();
                        }
                    }
                }
            }
        }

        /**
         * Converts an instance of {@link TestCase} into a corresponding portion
         * of a JUnit sourcefile. This is the root method for creating actual
         * test methods (as one testcase in JUnit will essentially correspond to
         * a single test method).
         * 
         * @param testCase
         * @throws JUnitConverterException
         */
        private void writeTestMethod(final TestCase testCase)
                throws JUnitConverterException {

            writeNewLine();

            /*
             * Write the method header.
             */
            final String methodName = "test"
                    + testCase.getMethod().getProgramMethod().getName();
            writeMethodHeader(new String[] { "@Test" }, "public", null, "void",
                    methodName + ID++, null, new String[] {
                            "NoSuchFieldException", "SecurityException",
                            "IllegalArgumentException",
                            "IllegalAccessException" });

            /*
             * Write the test fixture.
             */
            writeTestFixture(testCase);

            /*
             * Write the invocation of the method itself. If the method return
             * type is different from void, write a temporary variable to store
             * the result.
             */
            writeMethodInvocation(testCase);

            /*
             * Write the oracle
             */
            writeOracle(testCase);

            writeClosingBrace();
        }
    }

    private static JUnitConverter instance = null;

    public static JUnitConverter getInstance() {
        if (JUnitConverter.instance == null) {
            JUnitConverter.instance = new JUnitConverter();
        }
        return JUnitConverter.instance;
    }

    private JUnitConverter() {
    }

    /**
     * Convert an abstract test suite into a JUnit test suite.
     * 
     * @param the
     *            test suite to convert
     * @return the resulting JUnit test suite
     */
    @Override
    public String convert(final TestSuite testSuite)
            throws JUnitConverterException {

        return new JUnitGeneratorWorker().serviceConvert(testSuite);
    }
}