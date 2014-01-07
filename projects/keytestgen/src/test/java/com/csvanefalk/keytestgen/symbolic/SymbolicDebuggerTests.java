package com.csvanefalk.keytestgen.symbolic;

import com.csvanefalk.keytestgen.backend.IFrameworkConverter;
import com.csvanefalk.keytestgen.backend.ITestSuite;
import com.csvanefalk.keytestgen.backend.TestGenerator;
import com.csvanefalk.keytestgen.backend.TestGeneratorException;
import com.csvanefalk.keytestgen.backend.junit.JUnitConverter;
import com.csvanefalk.keytestgen.core.codecoverage.ICodeCoverageParser;
import org.junit.Assert;
import org.junit.Test;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

public class SymbolicDebuggerTests {

    private final String pathToExamples = "/home/christopher/git/key/examples/_testcase/set/";
    final TestGenerator testCaseGenerator = TestGenerator.getInstance();
    final IFrameworkConverter junitConverter = JUnitConverter.getInstance();
    final ICodeCoverageParser codeCoverageParser = ICodeCoverageParser.statementCoverageParser;

    @Test
    public void testStatementKindTest() throws TestGeneratorException {

        String classPath = "statementKindTest/test/StatementKindTest.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testWhileTestTest() throws TestGeneratorException {

        String classPath = "whileFalseTest/test/WhileFalseTest.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testWhileFalseTest() throws TestGeneratorException {

        String classPath = "whileTest/test/WhileTest.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testTryCatchFinally() throws TestGeneratorException {

        String classPath = "tryCatchFinally/test/TryCatchFinally.java";
        String methodName = "tryCatchFinally";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testThrowVariableTest() throws TestGeneratorException {

        String classPath = "throwVariableTest/test/ThrowVariableTest.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testThrowTest() throws TestGeneratorException {

        String classPath = "throwTest/test/ThrowTest.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testSwitchCaseTest() throws TestGeneratorException {

        String classPath = "switchCaseTest/test/SwitchCaseTest.java";
        String methodName = "switchCase";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testStaticMethodCall() throws TestGeneratorException {

        String classPath = "staticMethodCall/test/StaticMethodCall.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testStatements() throws TestGeneratorException {

        String classPath = "statements/test/FlatSteps.java";
        String methodName = "doSomething";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testSimpleNullPointerSplitTest() throws TestGeneratorException {

        String classPath = "simpleNullPointerSplitTest/test/SimpleNullPointerSplitTest.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testSimpleIf() throws TestGeneratorException {

        String classPath = "simpleIf/test/SimpleIf.java";
        String methodName = "min";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);
    }

    // @Test
    public void testRecursiveFibonacci_LONG_RUNNING_TEST() throws TestGeneratorException {

        String classPath = "recursiveFibonacci/test/RecursiveFibonacci.java";
        String methodName = "fibonacci10";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testNestedWhileTest() throws TestGeneratorException {

        String classPath = "nestedWhileTest/test/NestedWhileTest.java";
        String methodName = "mainNested";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testNestedForTest() throws TestGeneratorException {

        String classPath = "nestedForTest/test/NestedForTest.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testNestedDoWhileTest() throws TestGeneratorException {

        String classPath = "nestedDoWhileTest/test/NestedDoWhileTest.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testMethodHierarchyCallWithExceptionTest() throws TestGeneratorException {

        String classPath = "methodHierarchyCallWithExceptionTest/test/MethodHierarchyCallWithExceptionTest.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testMethodHierarchyCallTest() throws TestGeneratorException {

        String classPath = "methodHierarchyCallTest/test/MethodHierarchyCallTest.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testMethodFormatTest() throws TestGeneratorException {

        String classPath = "methodFormatTest/test/MethodFormatTest.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testMethodCallParallelTest() throws TestGeneratorException {

        String classPath = "methodCallParallelTest/test/MethodCallParallelTest.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testMethodCallOnObjectWithException() throws TestGeneratorException {

        String classPath = "methodCallOnObjectWithException/test/MethodCallOnObjectWithException.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    @Test
    public void testMethodCallOnObject() throws TestGeneratorException {

        String classPath = "methodCallOnObject/test/MethodCallOnObject.java";
        String methodName = "main";
        List<String> methods = new LinkedList<String>();
        methods.add(methodName);
        File file = loadFile(classPath);

        final List<ITestSuite> output = testCaseGenerator.generateTestSuite(file.getAbsolutePath(),
                                                                            codeCoverageParser,
                                                                            junitConverter,
                                                                            methods);

        write(output);
    }

    /**
     * Helper for loading files
     *
     * @param example
     * @return
     */
    private File loadFile(String example) {
        File file = new File(pathToExamples + example);
        Assert.assertTrue(file.exists());
        return file;
    }

    private void write(List<ITestSuite> toWrite) {
        // System.out.println(toWrite);
    }
}
