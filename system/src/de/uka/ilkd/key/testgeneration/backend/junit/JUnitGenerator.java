package de.uka.ilkd.key.testgeneration.backend.junit;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.testgeneration.backend.AbstractJavaSourceGenerator;
import de.uka.ilkd.key.testgeneration.backend.TestCase;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaClass;
import de.uka.ilkd.key.testgeneration.model.IModelObject;
import de.uka.ilkd.key.testgeneration.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelInstance;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelVariable;

/**
 * This singleton provides the functionality needed to produce test suites for
 * the JUnit framework.
 * 
 * @author christopher
 * 
 */
public class JUnitGenerator {

    public String generateJUnitSources(KeYJavaClass klass,
            LinkedList<TestCase> testCases) {

        return new JUnitGeneratorWorker().serviceConvertToJUnit(klass,
                testCases);
    }

    /**
     * Worker which services invocations of
     * {@link JUnitGenerator#convertToJUnit(List)}.
     * 
     * @author christopher
     * 
     */
    private static class JUnitGeneratorWorker extends
            AbstractJavaSourceGenerator {

        /**
         * The name of the class for which the test suite is being generated.
         * Kept for the purpose of naming and type declaration.
         */
        String className = "X";

        /**
         * Services invocations of
         * {@link JUnitGenerator#generateJUnitSources(KeYJavaClass, List)}
         * 
         * @param klass
         *            the class for which we are generating test cases
         * @param testCases
         *            the test cases to generate
         * @return a JUnit source file in String format
         */
        public String serviceConvertToJUnit(KeYJavaClass klass,
                LinkedList<TestCase> testCases) {

            /*
             * Safeguard
             */
            if (testCases.isEmpty()) {
                return "";
            }

            className = klass.getName();

            /*
             * Main processing loop
             */
            while (!testCases.isEmpty()) {

                /*
                 * Handle the test cases in parititions according to which
                 * method they deal with. We let a linked list hold the test
                 * cases that are to be included in the current class.
                 */
                LinkedList<TestCase> currentTests = new LinkedList<TestCase>();
                currentTests.add(testCases.pollFirst());
                while (!testCases.isEmpty()) {

                    /*
                     * Check if the next test case deals with the current
                     * method. If it does not, put it back and the queue and
                     * proceed to process the test cases we have extracted so
                     * far.
                     */
                    TestCase nextTestCase = testCases.pollFirst();
                    TestCase lastTestCase = currentTests.peekFirst();

                    if (nextTestCase.compareTo(lastTestCase) == 0) {

                        currentTests.add(nextTestCase);
                    } else {

                        testCases.addFirst(nextTestCase);
                        break;
                    }
                }

                String methodName = currentTests.get(0).getMethodName();

                /*
                 * Print the new class header
                 */
                writeClassHeader(null, "public", "", "Test_" + klass.getName()
                        + "_" + methodName);

                /*
                 * Create one test method for each test case.
                 */
                for (TestCase testCase : currentTests) {

                    writeTestMethod(testCase);
                }

                /*
                 * Create the fixutre repository for this class
                 */
                createFixtureRepository(currentTests);

                /*
                 * Close the class body.
                 */
                writeClosingBrace();
            }

            return getCurrentOutput();
        }

        /**
         * Converts an instance of {@link TestCase} into a corresponding portion
         * of a JUnit sourcefile. This is the root method for creating actual
         * test methods (as one testcase in JUnit will essentially correspond to
         * a single test method).
         * 
         * @param testCase
         */
        private void writeTestMethod(TestCase testCase) {

            writeLine("\n");

            /*
             * Write the method header.
             */
            String methodName = "test"
                    + testCase.getMethod().getProgramMethod().getName();
            writeMethodHeader(new String[] { "@Test" }, "public", null, "void",
                    methodName, null);

            /*
             * Write the method body.
             */
            writeTestFixture((Model) testCase.getModel());

            /*
             * Close the method.
             */
            writeClosingBrace();
        }

        /**
         * Writes the fixture portion of a JUnit test method. Primarily, this
         * involves declaring and instantiating variables and parameter values.
         * 
         * @param model
         *            {@link Model} instance representing the fixture
         */
        private void writeTestFixture(Model model) {

            for (IModelObject object : model.getVariables()) {
                writeVariableDeclaration((ModelVariable) object);
            }
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
            if (variable.getIdentifier().equals("self")) {
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
            if (isPrimitiveType(variable.getValue())) {
                instantiation = variable.getValue().toString();
            } else {
                if (variable.getValue() != null) {
                    String reference = ((ModelInstance) variable.getValue())
                            .getIdentifier();
                    instantiation = "getObjectInstance(" + reference + ");";
                } else {
                    instantiation = "null;";
                }
            }

            /*
             * Finally, print the complete declaration and instantiation
             */
            writeLine(declaration + " = " + instantiation + "\n");
        }

        /**
         * Sets up the fixture repository for a given test class. This
         * repository will contain the object instances needed for the test
         * cases to run.
         * 
         * @param testCases
         *            the test cases for the test class.
         */
        private void createFixtureRepository(LinkedList<TestCase> testCases) {

            /*
             * Safeguard from first invocation errors.
             */
            if (testCases.isEmpty()) {
                return;
            }

            /*
             * Write the HashMap for holding the object instances.
             */
            writeLine("\n");
            writeComment(
                    "KeYTestGen put me here to keep track of your object instances! Don't mind me :)",
                    true);
            writeLine("HashMap<Integer, Object> objectInstances = new HashMap<String,Object>()\n\n");

            /*
             * Write the method for retrieving the actual test instances.
             */
            writeLine("\n");
            writeComment(
                    "This method will retrieve an object instance corresponding to its reference ID.",
                    true);
            writeMethodHeader(null, "private", new String[] { "<T>" }, "T",
                    "getObjectInstance", new String[] { "int reference" });
            writeLine("return (T)objectInstances.get(reference)\n");
            writeClosingBrace();

            /*
             * Write the main init method for creating the repository of Object
             * instances.
             */
            writeLine("\n");
            writeMethodHeader(new String[] { "@BeforeClass" }, "public",
                    new String[] { "static" }, "void",
                    "createFixtureRepository", null);

            /*
             * Inside the init method, write the initializers for the individual
             * instances.
             */
            for (TestCase testCase : testCases) {
                createInstancesForModel((Model) testCase.getModel());
            }
            writeClosingBrace();
        }

        /**
         * Creates object instances for a {@link Model} instance.
         * 
         * @param model
         *            the model
         */
        private void createInstancesForModel(Model model) {

            for (IModelObject object : model.getVariables()) {
                ModelVariable variable = (ModelVariable) object;
                if (variable.getValue() instanceof ModelInstance) {
                    writeLine("\n");
                    writeModelInstantiation((ModelInstance) variable.getValue());
                }
            }
        }

        private void writeModelInstantiation(ModelInstance instance) {

            try {

                Class<?> instanceType;
                if (instance.getIdentifier().equals("self")) {
                    instanceType = Class.forName(className);
                } else {
                    instanceType = Class.forName(instance.getType());
                }
                writeOpeningBrace();
                writeLine("Integer identifier = " + instance.getIdentifier()
                        + ";\n");

                writeClosingBrace();

            } catch (ClassNotFoundException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
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
         * Checks if an objects runtime type is primitive.
         * 
         * @param object
         *            the object whose type to check
         * @return true if the runtime type is positive, false otherwise
         */
        private boolean isPrimitiveType(Object object) {
            return object.getClass() == Integer.class
                    || object.getClass() == Boolean.class
                    || object.getClass() == Byte.class
                    || object.getClass() == Long.class
                    || object.getClass() == Float.class
                    || object.getClass() == Double.class;
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
         * @throws JUnitGeneratorException
         */
        private boolean hasSetMethodForField(Object object, String fieldName)
                throws JUnitGeneratorException {

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
                throw new JUnitGeneratorException(stringBuilder.toString());
            }

            return true;
        }
    }
}