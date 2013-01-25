package de.uka.ilkd.key.testgeneration.backend.junit;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
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
            List<TestCase> testCases) {

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
                List<TestCase> testCases) {

            UtilityClassCreator utilityClassCreator = new UtilityClassCreator();

            /*
             * Print the class header
             */
            writeClassHeader(null, "public", "", klass.getName());

            /*
             * Create one test method for each test case.
             */
            for (TestCase testCase : testCases) {
                writeTestMethod(testCase);
            }

            /*
             * Close the class body.
             */
            writeClosingBrace();

            /*
             * Finalize the utility class, if it is needed.
             */
            appendToOutput(utilityClassCreator.getCurrentOutput());

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

            if (!"self".equals(variable.getIdentifier())) {

                /*
                 * Compile the lefthand side of the declaration.
                 */
                String declaration = variable.getType() + " "
                        + variable.getName();

                /*
                 * Compile the righthand side. What is done here will depend on
                 * the type of the value itself. Primitive types are trivial to
                 * process, and only involve printing the actual value
                 * associated with the variable. References are a different
                 * matter and require separate processing.
                 */
                String instantiation = "";
                if (isPrimitiveType(variable.getValue())) {
                    instantiation = variable.getValue().toString();
                } else {
                    // TODO: Process refs
                }

                /*
                 * Finally, print the complete declaration and instantiation
                 */
                writeComment(
                        "This is a comment with a whole lot of lines! In fact it has so many lines that we will have to split them over several different lines!!",
                        true);
                writeLine(declaration + " = " + instantiation + "\n");
            }
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

    }

    /**
     * Instances of this class are used in order to write any utility classes
     * needed for the generated test suite. Such utility classes are primarily
     * used in order to set up the test fixture.
     * 
     * @author christopher
     * 
     */
    private static class UtilityClassCreator extends
            AbstractJavaSourceGenerator {

        public UtilityClassCreator() {

            writeLine("\n\n\n\n");
            writeComment(
                    "Hello there! I am the FixtureFactory, and I was generated by KeYTestGen to help instantiate your test environment. You can ignore me, as I am only here to help. Please do not modify me, since this might cause your tests to stop running as they should! KiKi says hi by the way, we both hope you are having a lot of fun with KeY so far! :)",
                    true);

            writeClassHeader(null, "private", "final", "FixtureFactory");

            writeLine("\n");
            writeComment("Holds all object instances needed for the test suite to execute", true);
            writeLine("HashMap<String, Object> objectInstances = new HashMap<String,Object>()\n\n");
        }

        @Override
        protected String getCurrentOutput() {

            return super.getCurrentOutput() + "\n}";
        }

        /**
         * This method generates the logic to create an actual runtime object
         * based on the data provided in an {@link ModelInstance} object.
         * 
         * @param instance
         *            the instance to "instantiate"
         */
        private <T> T createInstance(ModelInstance instance) {

            String apa = createInstance(null);

            for (ModelVariable field : instance.getFields()) {

            }
            return null;
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