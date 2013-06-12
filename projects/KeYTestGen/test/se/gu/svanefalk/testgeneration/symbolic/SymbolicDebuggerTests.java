package se.gu.svanefalk.testgeneration.symbolic;

import java.io.File;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import se.gu.svanefalk.testgeneration.backend.IFrameworkConverter;
import se.gu.svanefalk.testgeneration.backend.TestGenerator;
import se.gu.svanefalk.testgeneration.backend.TestGeneratorException;
import se.gu.svanefalk.testgeneration.backend.junit.JUnitConverter;
import se.gu.svanefalk.testgeneration.core.codecoverage.ICodeCoverageParser;

public class SymbolicDebuggerTests {

    private final String pathToExamples = "/home/christopher/git/key/examples/_testcase/set/";
    final TestGenerator testCaseGenerator = TestGenerator.getInstance();
    final IFrameworkConverter junitConverter = new JUnitConverter();
    final ICodeCoverageParser codeCoverageParser = ICodeCoverageParser.statementCoverageParser;

    @Test
    public void testStatementKindTest() throws TestGeneratorException {

        String classPath = "statementKindTest/test/StatementKindTest.java";
        String methodName = "main";
        File file = loadFile(classPath);

        final List<String> output = testCaseGenerator.generatePartialTestSuite(
                file, codeCoverageParser, junitConverter, methodName);
    }
    
    @Test
    public void testWhileTestTest() throws TestGeneratorException {

        String classPath = "whileFalseTest/test/WhileFalseTest.java";
        String methodName = "main";
        File file = loadFile(classPath);

        final List<String> output = testCaseGenerator.generatePartialTestSuite(
                file, codeCoverageParser, junitConverter, methodName);
    }
    
    @Test
    public void testWhileFalseTest() throws TestGeneratorException {

        String classPath = "whileTest/test/WhileTest.java";
        String methodName = "main";
        File file = loadFile(classPath);

        final List<String> output = testCaseGenerator.generatePartialTestSuite(
                file, codeCoverageParser, junitConverter, methodName);
    }
    
    @Test
    public void testTryCatchFinally() throws TestGeneratorException {

        String classPath = "tryCatchFinally/test/TryCatchFinally.java";
        String methodName = "tryCatchFinally";
        File file = loadFile(classPath);

        final List<String> output = testCaseGenerator.generatePartialTestSuite(
                file, codeCoverageParser, junitConverter, methodName);
    }
    
    @Test
    public void testThrowVariableTest() throws TestGeneratorException {

        String classPath = "throwVariableTest/test/ThrowVariableTest.java";
        String methodName = "main";
        File file = loadFile(classPath);

        final List<String> output = testCaseGenerator.generatePartialTestSuite(
                file, codeCoverageParser, junitConverter, methodName);
    }
    
    @Test
    public void testThrowTest() throws TestGeneratorException {

        String classPath = "throwTest/test/ThrowTest.java";
        String methodName = "main";
        File file = loadFile(classPath);

        final List<String> output = testCaseGenerator.generatePartialTestSuite(
                file, codeCoverageParser, junitConverter, methodName);
    }
    
    @Test
    public void testSwitchCaseTest() throws TestGeneratorException {

        String classPath = "switchCaseTest/test/SwitchCaseTest.java";
        String methodName = "switchCase";
        File file = loadFile(classPath);

        final List<String> output = testCaseGenerator.generatePartialTestSuite(
                file, codeCoverageParser, junitConverter, methodName);
    }
    
    @Test
    public void testStaticMethodCall() throws TestGeneratorException {

        String classPath = "staticMethodCall/test/StaticMethodCall.java";
        String methodName = "main";
        File file = loadFile(classPath);

        final List<String> output = testCaseGenerator.generatePartialTestSuite(
                file, codeCoverageParser, junitConverter, methodName);
    }

    @Test
    public void testStatements() throws TestGeneratorException {

        String classPath = "statements/test/FlatSteps.java";
        String methodName = "doSomething";
        File file = loadFile(classPath);

        final List<String> output = testCaseGenerator.generatePartialTestSuite(
                file, codeCoverageParser, junitConverter, methodName);
    }
    
    @Test
    public void testSimpleNullPointerSplitTest() throws TestGeneratorException {

        String classPath = "simpleNullPointerSplitTest/test/SimpleNullPointerSplitTest.java";
        String methodName = "main";
        File file = loadFile(classPath);

        final List<String> output = testCaseGenerator.generatePartialTestSuite(
                file, codeCoverageParser, junitConverter, methodName);
    }
    
    @Test
    public void testSimpleIf() throws TestGeneratorException {

        String classPath = "simpleIf/test/SimpleIf.java";
        String methodName = "min";
        File file = loadFile(classPath);

        final List<String> output = testCaseGenerator.generatePartialTestSuite(
                file, codeCoverageParser, junitConverter, methodName);
    }
    
    @Test
    public void testRecursiveFibonacci_LONG_RUNNING_TEST() throws TestGeneratorException {

        String classPath = "recursiveFibonacci/test/RecursiveFibonacci.java";
        String methodName = "fibonacci10";
        File file = loadFile(classPath);

        final List<String> output = testCaseGenerator.generatePartialTestSuite(
                file, codeCoverageParser, junitConverter, methodName);
    }
    
    /**
     * Helper for loading files
     * @param example
     * @return
     */
    private File loadFile(String example) {
        File file = new File(pathToExamples + example);
        Assert.assertTrue(file.exists());
        return file;
    }
}
