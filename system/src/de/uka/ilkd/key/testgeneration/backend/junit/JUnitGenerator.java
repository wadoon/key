package de.uka.ilkd.key.testgeneration.backend.junit;

import java.util.List;

import de.uka.ilkd.key.testgeneration.backend.AbstractJavaSourceGenerator;
import de.uka.ilkd.key.testgeneration.backend.TestCase;
import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaClass;
import de.uka.ilkd.key.testgeneration.model.IModelObject;
import de.uka.ilkd.key.testgeneration.model.implementation.Model;
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

            writeLine("");

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
                writeLine(declaration + " = " + instantiation);
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
}