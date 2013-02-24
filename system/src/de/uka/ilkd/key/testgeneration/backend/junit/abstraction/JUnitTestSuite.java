package de.uka.ilkd.key.testgeneration.backend.junit.abstraction;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.testgeneration.StringConstants;
import de.uka.ilkd.key.testgeneration.backend.AbstractJavaSourceGenerator;
import de.uka.ilkd.key.testgeneration.backend.junit.JUnitConverter;
import de.uka.ilkd.key.testgeneration.backend.junit.JUnitConverterException;
import de.uka.ilkd.key.testgeneration.core.KeYJavaClass;
import de.uka.ilkd.key.testgeneration.core.KeYJavaMethod;
import de.uka.ilkd.key.testgeneration.core.coreinterface.TestCase;
import de.uka.ilkd.key.testgeneration.core.coreinterface.TestSuite;
import de.uka.ilkd.key.testgeneration.core.model.IModelObject;
import de.uka.ilkd.key.testgeneration.core.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelInstance;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelVariable;
import de.uka.ilkd.key.testgeneration.core.oraclegeneration.OracleGenerationTools;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.CNFTransformer;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.SimplifyConjunctionTransformer;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.SimplifyDisjunctionTransformer;
import de.uka.ilkd.key.testgeneration.core.parsers.transformers.TermTransformerException;
import de.uka.ilkd.key.testgeneration.core.parsers.visitors.KeYTestGenTermVisitor;

/**
 * Represents a JUnit test suite. It consists of a set of {@link JUnitTestCase}
 * instances, a set of imports, and a set of utility methods and state
 * variables.
 * 
 * @author christopher
 * 
 */
public class JUnitTestSuite {

    /**
     * Constructs a JUnit test suite from an abstract {@link TestSuite}.
     * 
     * @param testSuite
     */
    public JUnitTestSuite(TestSuite testSuite) {

    }

    /**
     * The imports needed for this test suite.
     */
    private final List<String> imports = new LinkedList<String>();

    /**
     * The test cases belonging to this test suite.
     */
    private final List<JUnitTestCase> testCases = new LinkedList<JUnitTestCase>();

    /**
     * @return the testCases
     */
    public List<JUnitTestCase> getTestCases() {
        return testCases;
    }

    /**
     * Adds a {@link JUnitTestCase} to the test suite.
     * 
     * @param declarationStatement
     * 
     */
    public void addTestCase(JUnitTestCase testCase) {
        testCases.add(testCase);
    }

    /**
     * @return the imports
     */
    public List<String> getImports() {
        return imports;
    }

    /**
     * Adds an import to the test suite.
     * 
     * @param declarationStatement
     * 
     */
    public void addImport(String importStatement) {
        imports.add(importStatement);
    }

    /**
     * Worker which constructs {@link JUnitTestSuite} instances from
     * {@link TestSuite} instances.
     * 
     * @author christopher
     * 
     */
    private static class JUnitGeneratorWorker extends
            AbstractJavaSourceGenerator {

        /**
         * Used to differentiate between the names of test cases.
         */
        private int ID = 0;

        /**
         * The name of the class for which the test suite is being generated.
         * Kept for the purpose of naming and type declaration.
         */
        private String className = "";

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
        public JUnitTestSuite constructJUnitTestSuite(TestSuite testSuite)
                throws JUnitConverterException {

            List<TestCase> testCases = testSuite.getTestCases();
            KeYJavaClass klass = testSuite.getJavaClass();
            KeYJavaMethod method = testSuite.getMethod();

            className = klass.getName();

            String methodName = testCases.get(0).getMethodName();

            /*
             * Convert the individual test cases
             */
            for (TestCase testCase : testCases) {

                convertToJUnitTestcase(testCase);
            }

            return null;
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
        private void convertToJUnitTestcase(TestCase testCase)
                throws JUnitConverterException {

            /*
             * Write the test fixture.
             */
            JUnitFixture fixture = constructFixture(testCase);

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
         * Constructs a {@link JUnitFixture} for a test case, based on the model
         * contained in it.
         * 
         * @param testCase
         * @return
         */
        private JUnitFixture constructFixture(TestCase testCase) {

            /*
             * Write the text fixture, using all relevant variables. Relevant
             * variables in this context includes the parameters for the method
             * (if any), as well as the root class itself.
             */
            for (IModelObject object : testCase.getModel().getVariables()) {

                ModelVariable variable = (ModelVariable) object;

                /*
                 * Construct a declaration statement for the variable.
                 */
                JUnitDeclarationStatement declarationStatement = new JUnitDeclarationStatement(
                        variable);

                if (isSelf(variable) || variable.isParameter()) {
                    writeVariableDeclaration(variable);
                }
            }
            return null;
        }

        /**
         * Writes the logic needed to invoke the method under test (MUT) for a
         * given testcase. If the MUT is of non-void type, this logic will
         * include a temporary variable for storing the result.
         * 
         * @param testCase
         */
        private void writeMethodInvocation(TestCase testCase) {

            String returnType = testCase.getMethod().getReturnType();
            String methodInvocation = "";
            if (!returnType.equals("void")) {
                methodInvocation += returnType + " " + EXECUTION_RESULT + " = ";
            }

            methodInvocation += SELF + "." + testCase.getMethodName() + "(";
            List<IProgramVariable> parameters = testCase.getMethod()
                    .getParameters();

            for (int i = 0; i < parameters.size(); i++) {
                String parameterName = parameters.get(i).name().toString();
                methodInvocation += parameterName;
                if (i != parameters.size() - 1) {
                    methodInvocation += ",";
                }
            }
            methodInvocation += ");" + NEWLINE;
            writeLine(methodInvocation);
        }

        /**
         * Writes a variable declaration and instantiation statement to a JUnit
         * test method.
         * 
         * @param variable
         *            variable to declare and instantiate
         */
        private void writeVariableDeclaration(ModelVariable variable) {

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
                    String reference = ((ModelInstance) variable.getValue())
                            .getIdentifier();
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
            writeLine(declaration + " = " + instantiation + ";" + NEWLINE);
        }

        /**
         * Sets up the fixture repository for a given test class. This
         * repository will contain the object instances needed for the test
         * cases to run.
         * 
         * @param testCases
         *            the test cases for the test class.
         */
        private void createFixtureRepository(List<TestCase> testCases) {

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
             * Write the main init method for creating the repository of Object
             * instances.
             */
            writeCreateInstanceRepositoryMethod(testCases);
        }

        /**
         * Writes the declaration and initialization of the Map holding the
         * concrete object instances used in this test class.
         */
        private void writeObjectInstanceMap() {

            writeLine(NEWLINE);
            writeComment(
                    "KeYTestGen put me here to keep track of your object instances! Don't mind me :)",
                    true);
            writeLine("private static HashMap<Integer, Object> objectInstances = new HashMap<Integer,Object>();"
                    + NEWLINE + NEWLINE);
        }

        /**
         * Writes the declaration and definition of the getObjectInstance(int
         * reference), which allows the test methods in the class to retrieve
         * the object instances they need in order to set up their fixtures.
         */
        private void writeGetObjectInstanceMethod() {

            writeLine(NEWLINE);
            writeComment(
                    "This method will retrieve an object instance corresponding to its reference ID.",
                    true);
            writeMethodHeader(null, "private",
                    new String[] { "static", "<T>" }, "T", "getObjectInstance",
                    new String[] { "int reference" }, null);
            writeLine("return (T)objectInstances.get(reference);" + NEWLINE);
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
        private void writeTestOracle(TestCase testCase)
                throws JUnitConverterException {

            /*
             * Delegate oracle generation to the Term visitor.
             */
            List<String> assertions = new OracleGenerationVisitor(testCase)
                    .generateOracle();

            writeLine("Assert.assertTrue(" + NEWLINE);
            for (String assertion : assertions) {
                writeLine(assertion + NEWLINE);
            }
            writeLine(");" + NEWLINE);
        }

        /**
         * Writes the createInstanceRepository() method, which is responsible
         * for creating and instantiating all the concrete object instances used
         * in the test fixtures of the test methods.
         * 
         * @param testCases
         */
        private void writeCreateInstanceRepositoryMethod(
                List<TestCase> testCases) {

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
            List<ModelInstance> instances = collectInstances(testCases);

            /*
             * Write the instantiation of the instances.
             */
            writeComment(
                    "Instantiate and insert the raw object instances into the repository. ",
                    false);
            for (ModelInstance instance : instances) {
                String toImport = instance.getType();
                imports.add(toImport);
                writeObjectInstantiation(instance);
            }

            /*
             * Write the field-instantiations for the same instances, concluding
             * the fixture setup procedure.
             */
            writeComment(
                    "Finalize the repository setup by setting up the relevant fields of each object instance.. ",
                    false);
            for (ModelInstance instance : instances) {
                if (!instance.getFields().isEmpty()) {
                    writeObjectFieldInstantiation(instance);
                }
            }

            writeClosingBrace();
        }

        /**
         * Given a set of {@link TestCase} instances, this method will extract
         * put all {@link ModelInstance} declared in the model of each testcase
         * into a single list.
         * 
         * @param testCases
         *            the test cases
         * @return a list of all instances declared in all test cases models
         */
        private List<ModelInstance> collectInstances(List<TestCase> testCases) {

            List<ModelInstance> instances = new LinkedList<ModelInstance>();
            for (TestCase testCase : testCases) {
                List<ModelInstance> collectedInstances = extractInstancesFromModel((Model) testCase
                        .getModel());
                instances.addAll(collectedInstances);
            }

            return instances;
        }

        /**
         * Given a {@link Model}, this method will extract all instances of
         * {@link ModelInstance} from it.
         * 
         * @param model
         * @return
         */
        private List<ModelInstance> extractInstancesFromModel(Model model) {

            List<ModelInstance> instances = new LinkedList<ModelInstance>();
            for (IModelObject object : model.getVariables()) {
                ModelVariable variable = (ModelVariable) object;
                if (variable.getValue() instanceof ModelInstance) {
                    instances.add((ModelInstance) variable.getValue());
                }
            }
            return instances;
        }

        /**
         * Writes the logic needed to instantiate an object and put it into the
         * instance Map.
         * 
         * @param instance
         *            the object instance to encode
         */
        private void writeObjectInstantiation(ModelInstance instance) {

            /*
             * Indicates whether or not this instance corresponds to the Java
             * class being tested (as we treat this one separately).
             */

            writeLine("objectInstances.put(" + instance.getIdentifier() + ","
                    + " new " + instance.getTypeName() + "());" + NEWLINE);
        }

        /**
         * Given an object instance, this method will properly setup this
         * instances by setting any mentioned fields to their expected values.
         * 
         * @param instance
         */
        private void writeObjectFieldInstantiation(ModelInstance instance) {

            /*
             * To avoid any potential namespace clashes, we let each
             * instantiation take place in its own scope.
             */
            writeOpeningBrace();

            /*
             * Write logic to fetch the actual instance of the instance.
             */
            writeLine(instance.getTypeName() + " instance = getObjectInstance("
                    + instance.getIdentifier() + ");" + NEWLINE);

            /*
             * Write reflection code for each relevant field of the instance, in
             * order to set it up properly.
             */
            for (ModelVariable field : instance.getFields()) {

                if (!field.isParameter()) {
                    String variableName = field.getName();
                    writeLine(NEWLINE);
                    writeLine("Field " + variableName + " = "
                            + "instance.getClass().getDeclaredField(" + "\""
                            + variableName + "\"" + ");\n");
                    writeLine(variableName + ".setAccessible(true);" + NEWLINE);

                    /*
                     * When it comes to setting the value, different courses of
                     * action are needed for primitive and reference type
                     * variables. Reference types will be encoded as a fetch of
                     * the relevant object instance using the getObjectInstance
                     * method. Primitive types will simply be encoded in terms
                     * of their primitive values.
                     */
                    if (field.getValue() instanceof ModelInstance) {

                        ModelInstance instanceField = (ModelInstance) field
                                .getValue();
                        writeLine(variableName + ".set(instance, "
                                + "getObjectInstance("
                                + instanceField.getIdentifier() + ") " + ");"
                                + NEWLINE);
                    } else {
                        writeLine(variableName + ".set(instance, "
                                + field.getValue() + ");" + NEWLINE);
                    }
                }
            }

            writeClosingBrace();
            writeLine(NEWLINE);
        }

        @Override
        protected String getCurrentOutput() {

            StringBuilder builder = new StringBuilder();

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
            for (String importt : imports) {
                builder.append("import ");
                builder.append(importt);
                builder.append(";\n");
            }
            builder.append(NEWLINE);
            builder.append(super.getCurrentOutput());

            return builder.toString();
        }

        private boolean isSelf(ModelVariable variable) {
            return variable.getIdentifier().equals("self");
        }

        /**
         * Investigates if a given object has a setter for a specific field.
         * This method will do it's best to find such a method, but in order for
         * it to return true, it is necessary that the method is appropriately
         * named.
         * 
         * @param object
         *            the object to check
         * @param fieldName
         *            the field to find a setter for
         * @return true if a setter was found, false otherwise
         * @throws JUnitConverterException
         */
        private boolean hasSetMethodForField(Object object, String fieldName)
                throws JUnitConverterException {

            try {

                /*
                 * Get the field itself.
                 */
                Field field = object.getClass().getField(fieldName);

                /*
                 * Attempt to find the setter for the field.
                 */
                String setterName = "set"
                        + fieldName.substring(0, 1).toUpperCase()
                        + fieldName.substring(1);

                Method setter = object.getClass().getMethod(setterName,
                        field.getType());

            } catch (NoSuchMethodException e) {

                return false;

            } catch (NoSuchFieldException e) {

                return false;

            } catch (SecurityException e) {
                StringBuilder stringBuilder = new StringBuilder();
                stringBuilder
                        .append("Security violation when trying to reflect on object of type: ");
                stringBuilder.append(object.getClass());
                stringBuilder
                        .append(" please review your Java security settings!");
                throw new JUnitConverterException(stringBuilder.toString());
            }

            return true;
        }

        /**
         * Attempts to find a no-args constructor for a target type.
         * 
         * @param klass
         *            the type for which to find the constructor
         * @return the constructor
         */
        private Constructor<?> getNoArgsConstructor(Class<?> klass) {

            for (Constructor<?> constructor : klass.getConstructors()) {

                if (constructor.getParameterTypes().length == 0) {
                    return constructor;
                }
            }
            return null;
        }

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

            public OracleGenerationVisitor(TestCase testCase) {
                this.testCase = testCase;

                parameterNames = new LinkedList<String>();
                List<IProgramVariable> variables = testCase.getMethod()
                        .getParameters();
                for (IProgramVariable variable : variables) {
                    parameterNames.add(variable.name().toString());
                }
            }

            public List<String> generateOracle() throws JUnitConverterException {

                try {

                    /*
                     * Simplify the postcondition
                     */
                    Term oracle = testCase.getOracle();
                    Term simplifiedOracle = OracleGenerationTools
                            .simplifyPostCondition(oracle, SEPARATOR);

                    /*
                     * Put it into Conjunctive Normal Form
                     */
                    simplifiedOracle = new CNFTransformer()
                            .transform(simplifiedOracle);

                    /*
                     * Simplify the disjunctions in the postcondition
                     */
                    simplifiedOracle = new SimplifyDisjunctionTransformer()
                            .transform(simplifiedOracle);

                    /*
                     * Simplify the remaining conjunctions
                     */
                    simplifiedOracle = new SimplifyConjunctionTransformer()
                            .transform(simplifiedOracle);

                    /*
                     * Traverse the postcondition(s) in the testcase, filling
                     * the buffer with the encoded terms.
                     */
                    simplifiedOracle.execPreOrder(this);

                    /*
                     * Process and turn the buffer into a String of boolean Java
                     * statements. Split this assertion into units, and store
                     * them as a linked list. Return the resulting list.
                     */
                    String assertionString = processBuffer();
                    String[] assertionArray = assertionString.split(NEWLINE);
                    List<String> assertions = new LinkedList<String>();
                    for (String assertion : assertionArray) {
                        assertions.add(assertion);
                    }

                    return assertions;

                } catch (TermTransformerException e) {

                    throw new JUnitConverterException(e.getMessage());
                }
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
                    String next = buffer.pollFirst();

                    /*
                     * Process unary operators
                     */
                    if (next.equals(NOT)) {
                        String statement = processBuffer();
                        return "!(" + statement + ")";

                        /*
                         * Process binary operators
                         */
                    } else if (operators.contains(next)) {
                        String lefthand = processBuffer();
                        String righthand = processBuffer();

                        if (next.equals(AND)) {
                            return lefthand + " && " + righthand;

                        } else if (next.equals(OR)) {
                            return lefthand + " || " + righthand;

                        } else if (next.equals(EQUALS)) {
                            return "(" + lefthand + " == " + righthand + ")"
                                    + NEWLINE;

                        } else if (next.equals(GREATER_OR_EQUALS)) {
                            return "(" + lefthand + " >= " + righthand + ")"
                                    + NEWLINE;

                        } else if (next.equals(LESS_OR_EQUALS)) {
                            return "(" + lefthand + " <= " + righthand + ")"
                                    + NEWLINE;

                        } else if (next.equals(GREATER_THAN)) {
                            return "(" + lefthand + " > " + righthand + ")"
                                    + NEWLINE;

                        } else if (next.equals(LESS_THAN)) {
                            return "(" + lefthand + " < " + righthand + ")"
                                    + NEWLINE;

                        } else if (next.equals(ADDITION)) {
                            return "(" + lefthand + " < " + righthand + ")"
                                    + NEWLINE;

                        } else if (next.equals(SUBTRACTION)) {
                            return "(" + lefthand + " < " + righthand + ")"
                                    + NEWLINE;

                        } else if (next.equals(DIVISION)) {
                            return "(" + lefthand + " < " + righthand + ")"
                                    + NEWLINE;

                        } else if (next.equals(MULTIPLICATION)) {
                            return "(" + lefthand + " < " + righthand + ")"
                                    + NEWLINE;
                        }

                        /*
                         * If none of the above were trapped, the operator is an
                         * identifier, and returned as such.
                         */
                    } else {
                        if (next.equals("result")) {
                            return RESULT;
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
            public void visit(Term visited) {

                if (isAnd(visited)) {
                    buffer.add(AND);

                } else if (isOr(visited)) {
                    buffer.add(OR);

                } else if (isGreaterOrEquals(visited)) {
                    buffer.add(GREATER_OR_EQUALS);

                } else if (isGreaterThan(visited)) {
                    buffer.add(GREATER_THAN);

                } else if (isLessOrEquals(visited)) {
                    buffer.add(LESS_OR_EQUALS);

                } else if (isLessThan(visited)) {
                    buffer.add(LESS_THAN);

                } else if (isEquals(visited)) {
                    buffer.add(EQUALS);

                } else if (isNot(visited)) {
                    buffer.add(NOT);

                } else if (isParamaterValue(visited)) {
                    buffer.add(visited.op().name().toString());

                } else if (isLocationVariable(visited)
                        && isPrimitiveType(visited)) {
                    buffer.add(visited.op().name().toString());

                } else if (isSortDependingFunction(visited)) {
                    String identifier = resolveIdentifierString(visited,
                            StringConstants.FIELD_SEPARATOR.toString());
                    buffer.add(identifier);

                } else if (isResult(visited)) {
                    buffer.add(EXECUTION_RESULT);
                }
            }

            private boolean isParamaterValue(Term term) {

                String name = term.op().name().toString();

                return parameterNames.contains(name);
            }

        }
    }
}