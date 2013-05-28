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
        String className = "StatementKindTest";
        String methodName = "main";
        File file = loadFile(classPath);

        final List<String> output = testCaseGenerator.generatePartialTestSuite(
                file, codeCoverageParser, junitConverter, methodName);
    }

    private File loadFile(String example) {
        File file = new File(pathToExamples + example);
        Assert.assertTrue(file.exists());
        return file;
    }
}
