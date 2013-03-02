package de.uka.ilkd.key.testgeneration.backend.junit;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.testgeneration.StringConstants;
import de.uka.ilkd.key.testgeneration.backend.AbstractJavaSourceGenerator;
import de.uka.ilkd.key.testgeneration.backend.IFrameworkConverter;
import de.uka.ilkd.key.testgeneration.core.classabstraction.KeYJavaClass;
import de.uka.ilkd.key.testgeneration.core.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelInstance;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelVariable;
import de.uka.ilkd.key.testgeneration.core.oraclegeneration.OracleGenerator;
import de.uka.ilkd.key.testgeneration.core.testsuiteabstraction.TestCase;
import de.uka.ilkd.key.testgeneration.core.testsuiteabstraction.TestSuite;
import de.uka.ilkd.key.testgeneration.util.parsers.AbstractTermParser;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.ConjunctionNormalFormTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.SimplifyConjunctionTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.SimplifyDisjunctionTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.TermTransformerException;
import de.uka.ilkd.key.testgeneration.util.parsers.visitors.KeYTestGenTermVisitor;

/**
 * This singleton provides the functionality needed to produce test suites for
 * the JUnit framework.
 * 
 * @author christopher
 * 
 */
public class JUnitConverter implements IFrameworkConverter {

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
         * {@link Term} visitor which converts a postcondition, expressed as a
         * {@link Term}, into a functional test case oracle in executable Java
         * code.
         * 
         * @author christopher
         * 
         */
        private static class OracleGenerationVisitor extends
                KeYTestGenTermVisitor {

            /**
             * Test case associated with this visitor;
             */
            private final TestCase testCase;

            /**
             * The names of the parameters declared in the testCase associated
             * with this visitor.
             */
            private final List<String> parameterNames;

            /**
             * Separator between instance names, and the names of their fields.
             */
            private final static String SEPARATOR = "-";

            /**
             * Buffer for holding generated Java code
             */
            LinkedList<String> buffer = new LinkedList<String>();

            public OracleGenerationVisitor(final TestCase testCase) {
                this.testCase = testCase;

                parameterNames = new LinkedList<String>();
                final List<IProgramVariable> variables = testCase.getMethod()
                        .getParameters();
                for (final IProgramVariable variable : variables) {
                    parameterNames.add(variable.name().toString());
                }
            }

            public String generateOracle() throws JUnitConverterException {

                /*
                 * Simplify the postcondition
                 */
                final Term oracle = testCase.getOracle();
                /*
                 * Traverse the postcondition(s) in the testcase, filling the
                 * buffer with the encoded terms.
                 */
                oracle.execPreOrder(this);

                return processBuffer();
            }

            private boolean isParamaterValue(final Term term) {

                final String name = term.op().name().toString();

                return parameterNames.contains(name);
            }

            /**
             * Recursively unwind the buffer, turning the order of encoded
             * statements and identifiers into a semantically equivalent Java
             * statement.
             * 
             * @return
             */
            private String processBuffer() {

                if (!buffer.isEmpty()) {
                    final String next = buffer.pollFirst();

                    /*
                     * Process unary operators
                     */
                    if (next.equals(AbstractTermParser.NOT)) {
                        final String statement = processBuffer();
                        return "!(" + statement + ")";

                        /*
                         * Process binary operators
                         */
                    } else if (AbstractTermParser.operators.contains(next)) {
                        final String lefthand = processBuffer();
                        final String righthand = processBuffer();

                        if (next.equals(AbstractTermParser.AND)) {
                            return lefthand + " && " + righthand;

                        } else if (next.equals(AbstractTermParser.OR)) {
                            return lefthand + " || " + righthand;

                        } else if (next.equals(AbstractTermParser.EQUALS)) {
                            return "(" + lefthand + " == " + righthand + ")";

                        } else if (next
                                .equals(AbstractTermParser.GREATER_OR_EQUALS)) {
                            return "(" + lefthand + " >= " + righthand + ")";

                        } else if (next
                                .equals(AbstractTermParser.LESS_OR_EQUALS)) {
                            return "(" + lefthand + " <= " + righthand + ")";

                        } else if (next.equals(AbstractTermParser.GREATER_THAN)) {
                            return "(" + lefthand + " > " + righthand + ")";

                        } else if (next.equals(AbstractTermParser.LESS_THAN)) {
                            return "(" + lefthand + " < " + righthand + ")";

                        } else if (next.equals(AbstractTermParser.ADDITION)) {
                            return "(" + lefthand + " < " + righthand + ")";

                        } else if (next.equals(AbstractTermParser.SUBTRACTION)) {
                            return "(" + lefthand + " < " + righthand + ")";

                        } else if (next.equals(AbstractTermParser.DIVISION)) {
                            return "(" + lefthand + " < " + righthand + ")";

                        } else if (next
                                .equals(AbstractTermParser.MULTIPLICATION)) {
                            return "(" + lefthand + " < " + righthand + ")";
                        }

                        /*
                         * If none of the above were trapped, the operator is an
                         * identifier, and returned as such.
                         */
                    } else {
                        if (next.equals("result")) {
                            return AbstractTermParser.RESULT;
                        }
                        return next;
                    }
                }

                /*
                 * Default case (iff. the buffer is empty)
                 */
                return "";
            }

            /**
             * Generate a textual representation for each relevant node
             */
            @Override
            public void visit(final Term visited) {

                if (isAnd(visited)) {
                    buffer.add(AbstractTermParser.AND);

                } else if (isOr(visited)) {
                    buffer.add(AbstractTermParser.OR);

                } else if (isGreaterOrEquals(visited)) {
                    buffer.add(AbstractTermParser.GREATER_OR_EQUALS);

                } else if (isGreaterThan(visited)) {
                    buffer.add(AbstractTermParser.GREATER_THAN);

                } else if (isLessOrEquals(visited)) {
                    buffer.add(AbstractTermParser.LESS_OR_EQUALS);

                } else if (isLessThan(visited)) {
                    buffer.add(AbstractTermParser.LESS_THAN);

                } else if (isEquals(visited)) {
                    buffer.add(AbstractTermParser.EQUALS);

                } else if (isNot(visited)) {
                    buffer.add(AbstractTermParser.NOT);

                } else if (isParamaterValue(visited)) {
                    buffer.add(visited.op().name().toString());

                } else if (isLocationVariable(visited)
                        && AbstractTermParser.isPrimitiveType(visited)) {
                    buffer.add(visited.op().name().toString());

                } else if (isSortDependingFunction(visited)) {
                    final String identifier = AbstractTermParser
                            .resolveIdentifierString(visited,
                                    StringConstants.FIELD_SEPARATOR.toString());
                    buffer.add(identifier);

                } else if (isResult(visited)) {
                    buffer.add(JUnitGeneratorWorker.EXECUTION_RESULT);
                }
            }

        }

        /**
         * Used to differentiate between the names of test cases.
         */
        private int ID = 0;

        /**
         * The name of the class for which the test suite is being generated.
         * Kept for the purpose of naming and type declaration.
         */
        private String className = "X";

        /**
         * Imports to be included in this test class
         */
        private final HashSet<String> imports = new HashSet<String>();

        /**
         * The name of the root variable (i.e. the variable pointing to the
         * instane of the object that has the methods to be tested).
         */
        private static final String SELF = "self";

        /**
         * The name of the container for the result value (if any) resulting
         * from the invocation of a method being tested. This value is used in
         * the assertion process, and must not conflict with the names of any
         * parameter values.
         */
        private static final String EXECUTION_RESULT = "result";

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
                final List<ModelInstance> collectedInstances = extractInstancesFromModel(testCase
                        .getModel());
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
            writeObjectInstanceMap();

            /*
             * Write the method for retrieving the actual test instances.
             */
            writeGetObjectInstanceMethod();

            /*
             * Write the method for setting fields of objects.
             */
            writeSetFieldMethod();

            /*
             * Write the main init method for creating the repository of Object
             * instances.
             */
            writeCreateInstanceRepositoryMethod(testCases);
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

        private boolean isSelf(final ModelVariable variable) {
            return variable.getIdentifier().equals("self");
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
         * Writes the createInstanceRepository() method, which is responsible
         * for creating and instantiating all the concrete object instances used
         * in the test fixtures of the test methods.
         * 
         * @param testCases
         */
        private void writeCreateInstanceRepositoryMethod(
                final List<TestCase> testCases) {

            writeComment(
                    "This method will set up the entire repository of object instances needed to execute the test cases declared above.",
                    true);

            /*
             * Write the method header. Observe the annotation.
             */
            writeMethodHeader(new String[] { "@BeforeClass" }, "public",
                    new String[] { "static" }, "void",
                    "createFixtureRepository", null, new String[] {
                            "NoSuchFieldException", "SecurityException",
                            "IllegalArgumentException",
                            "IllegalAccessException" });

            /*
             * Write the object instantiations and the routines for storing them
             * in the instance Map.
             */
            final List<ModelInstance> instances = collectInstances(testCases);

            /*
             * Write the instantiation of the instances.
             */
            writeComment(
                    "Instantiate and insert the raw object instances into the repository. After this, finalize the repository setup by setting up the relevant fields of each object instance as necessary ",
                    false);
            for (final ModelInstance instance : instances) {
                final String toImport = instance.getType();
                imports.add(toImport);
                writeObjectInstantiation(instance);
            }

            /*
             * Write the field-instantiations for the same instances, concluding
             * the fixture setup procedure.
             */
            for (final ModelInstance instance : instances) {
                if (!instance.getFields().isEmpty()) {
                    writeObjectFieldInstantiation(instance);
                }
            }

            writeClosingBrace();
        }

        /**
         * Writes the declaration and definition of the getObjectInstance(int
         * reference), which allows the test methods in the class to retrieve
         * the object instances they need in order to set up their fixtures.
         */
        private void writeGetObjectInstanceMethod() {

            writeLine(AbstractJavaSourceGenerator.NEWLINE);
            writeComment(
                    "This method will retrieve an object instance corresponding to its reference ID.",
                    true);
            writeMethodHeader(null, "private",
                    new String[] { "static", "<T>" }, "T", "getObjectInstance",
                    new String[] { "int reference" }, null);
            writeLine("return (T)objectInstances.get(reference);"
                    + AbstractJavaSourceGenerator.NEWLINE);
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
            final List<IProgramVariable> parameters = testCase.getMethod()
                    .getParameters();

            for (int i = 0; i < parameters.size(); i++) {
                final String parameterName = parameters.get(i).name()
                        .toString();
                methodInvocation += parameterName;
                if (i != parameters.size() - 1) {
                    methodInvocation += ",";
                }
            }
            methodInvocation += ");" + AbstractJavaSourceGenerator.NEWLINE;
            writeLine(methodInvocation);
        }

        /**
         * Given an object instance, this method will properly setup this
         * instances by setting any mentioned fields to their expected values.
         * 
         * @param instance
         */
        private void writeObjectFieldInstantiation(final ModelInstance instance) {

            /*
             * To avoid any potential namespace clashes, we let each
             * instantiation take place in its own scope.
             */
            writeOpeningBrace();

            /*
             * Write logic to fetch the actual instance of the instance.
             */
            writeLine(instance.getTypeName() + " instance = getObjectInstance("
                    + instance.getIdentifier() + ");"
                    + AbstractJavaSourceGenerator.NEWLINE);

            /*
             * Write reflection code for each relevant field of the instance, in
             * order to set it up properly.
             */
            for (final ModelVariable field : instance.getFields()) {

                if (!field.isParameter()) {

                    /*
                     * When it comes to setting the value, different courses of
                     * action are needed for primitive and reference type
                     * variables. Reference types will be encoded as a fetch of
                     * the relevant object instance using the getObjectInstance
                     * method. Primitive types will simply be encoded in terms
                     * of their primitive values.
                     */
                    final String variableName = field.getName();
                    if (field.getValue() instanceof ModelInstance) {

                        final ModelInstance instanceField = (ModelInstance) field
                                .getValue();
                        writeLine("setFieldValue(instance, " + "\""
                                + variableName + "\"" + ", "
                                + "getObjectInstance("
                                + instanceField.getIdentifier() + ") " + ");"
                                + AbstractJavaSourceGenerator.NEWLINE);
                    } else {
                        writeLine("setFieldValue(instance, " + "\""
                                + variableName + "\"" + ", " + field.getValue()
                                + ");" + AbstractJavaSourceGenerator.NEWLINE);
                    }
                }
            }

            writeClosingBrace();
            writeLine(AbstractJavaSourceGenerator.NEWLINE);
        }

        /**
         * Writes the declaration and initialization of the Map holding the
         * concrete object instances used in this test class.
         */
        private void writeObjectInstanceMap() {

            writeLine(AbstractJavaSourceGenerator.NEWLINE);
            writeComment(
                    "KeYTestGen2 put me here to keep track of your object instances! Don't mind me :)",
                    true);
            writeLine("private static HashMap<Integer, Object> objectInstances = new HashMap<Integer,Object>();"
                    + AbstractJavaSourceGenerator.NEWLINE
                    + AbstractJavaSourceGenerator.NEWLINE);
        }

        /**
         * Writes the logic needed to instantiate an object and put it into the
         * instance Map.
         * 
         * @param instance
         *            the object instance to encode
         */
        private void writeObjectInstantiation(final ModelInstance instance) {

            /*
             * Indicates whether or not this instance corresponds to the Java
             * class being tested (as we treat this one separately).
             */

            writeLine("objectInstances.put(" + instance.getIdentifier() + ","
                    + " new " + instance.getTypeName() + "());"
                    + AbstractJavaSourceGenerator.NEWLINE);
        }

        /**
         * Writes the setField method.
         */
        private void writeSetFieldMethod() {

            writeComment("Sets a field of some object to a given value", true);
            writeMethodHeader(null, "private", new String[] { "static" },
                    "void", "setFieldValue", new String[] { "Object instance",
                            "String fieldName", "Object value" }, new String[] {
                            "NoSuchFieldException", "SecurityException",
                            "IllegalArgumentException",
                            "IllegalAccessException" });

            writeLine("Field field = instance.getClass().getDeclaredField(fieldName);"
                    + AbstractJavaSourceGenerator.NEWLINE);
            writeLine("field.setAccessible(true);"
                    + AbstractJavaSourceGenerator.NEWLINE);
            writeLine("field.set(instance, value );"
                    + AbstractJavaSourceGenerator.NEWLINE);

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
             * Write the text fixture, using all relevant variables. Relevant
             * variables in this context includes the parameters for the method
             * (if any), as well as the root class itself.
             */
            for (final ModelVariable variable : testCase.getModel()
                    .getVariables()) {
                if (isSelf(variable) || variable.isParameter()) {
                    writeVariableDeclaration(variable);
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

            writeLine(AbstractJavaSourceGenerator.NEWLINE);

            /*
             * Write the method header.
             */
            final String methodName = "test"
                    + testCase.getMethod().getProgramMethod().getName();
            writeMethodHeader(new String[] { "@Test" }, "public", null, "void",
                    methodName + ID++, null, null);

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
            writeTestOracle(testCase);

            writeClosingBrace();
        }

        /**
         * Writes the Java code constituting the test oracle for a given test
         * case.
         * 
         * @param testCase
         *            the test case
         * @throws JUnitConverterException
         */
        private void writeTestOracle(final TestCase testCase)
                throws JUnitConverterException {

            /*
             * Delegate oracle generation to the Term visitor.
             */
            final String oracleString = new OracleGenerationVisitor(testCase)
                    .generateOracle();

            final String[] conjunctions = oracleString.split("&&");
            for (final String conjunction : conjunctions) {

                writeLine("Assert.assertTrue("
                        + AbstractJavaSourceGenerator.NEWLINE);
                final String[] disjunctions = conjunction.split("\\|\\|");

                for (int i = 0; i < disjunctions.length; i++) {

                    String toWrite = AbstractJavaSourceGenerator.TAB
                            + disjunctions[i].trim();
                    if (i + 1 != disjunctions.length) {
                        toWrite += " ||";
                    }
                    writeLine(toWrite + AbstractJavaSourceGenerator.NEWLINE);
                }
                writeLine(");" + AbstractJavaSourceGenerator.NEWLINE);
            }
            writeLine(AbstractJavaSourceGenerator.NEWLINE);
        }

        /**
         * Writes a variable declaration and instantiation statement to a JUnit
         * test method.
         * 
         * @param variable
         *            variable to declare and instantiate
         */
        private void writeVariableDeclaration(final ModelVariable variable) {

            /*
             * Compile the lefthand side of the declaration. The "self" type
             * needs special treatment.
             */
            String declaration = "";
            if (isSelf(variable)) {
                declaration = className + " self";
            } else {
                declaration = variable.getType() + " " + variable.getName();
            }

            /*
             * Compile the righthand side. What is done here will depend on the
             * type of the value itself. Primitive types are trivial to process,
             * and only involve printing the actual value associated with the
             * variable. References are a different matter and require separate
             * processing.
             */
            String instantiation = "";
            if (variable.getValue() instanceof ModelInstance) {
                if (variable.getValue() != null) {
                    final String reference = ((ModelInstance) variable
                            .getValue()).getIdentifier();
                    instantiation = "getObjectInstance(" + reference + ")";
                } else {
                    instantiation = "null";
                }
            } else {
                instantiation = variable.getValue().toString();
            }

            /*
             * Finally, print the complete declaration and instantiation
             */
            writeLine(declaration + " = " + instantiation + ";"
                    + AbstractJavaSourceGenerator.NEWLINE);
        }
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