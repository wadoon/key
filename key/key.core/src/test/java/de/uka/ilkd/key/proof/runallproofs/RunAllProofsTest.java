package de.uka.ilkd.key.proof.runallproofs;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.*;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.parsing.SyntaxErrorReporter;
import org.antlr.v4.runtime.CharStreams;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Tag;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.Date;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * <p>
 * This class uses the provided example files from KeY for test purpose on the same way as the
 * bin/runAllProofs.pl does it.
 * </p>
 *
 * <p>
 * RunAllProofs documentation can be found at the following location in KeY git repository:
 * key/doc/README.runAllProofs
 * </p>
 *
 * <p>
 * The files to test are listed in: <br />
 * $KEY_HOME/key.core/src/test/resources/testcase/runallproofs/automaticJAVADL.txt
 * </p>
 *
 * <p>
 * The test steps for each defined test file are:
 * <ol>
 * <li>Create a copy with extension ".auto.key". The file contains the default settings from
 * examples/index/headerJavaDL.txt if required.</li>
 * <li>A new Java process is started for each test file. It executes Main#main with the file as
 * parameter and additional parameter {@code auto}.</li>
 * <li>The process termination result must be {@code 0} if the proof is closed and something
 * different otherwise. This value is used to determine the test result.</li>
 * </ol>
 * </p>
 * <p>
 * This class can be executed as "JUnit plug-in test" without extra configurations. For execution as
 * normal "Junit test" it is required to define the system properties "key.home" and "key.lib" like:
 * {@code "-Dkey.home=D:/Forschung/GIT/KeY" "-Dkey.lib=D:/Forschung/Tools/KeY-External Libs"} .
 * </p>
 * <p>
 * This class itself does not define testcases. The class has subclasses which define test cases for
 * different run-all-proof scenarios.
 *
 * @author Martin Hentschel
 * @see ListRunAllProofsTestCases
 */
@Tag("slow")
public abstract class RunAllProofsTest {
    public static final String VERBOSE_OUTPUT_KEY = "verboseOutput";
    public static final String IGNORE_KEY = "ignore";
    private static final Logger LOGGER = LoggerFactory.getLogger(RunAllProofsTest.class);


    /**
     * Creates a set of constructor parameters for this class. Uses JUnits parameterized test case
     * mechanism for to create several test cases from a set of data. {@link Object#toString()} of
     * first constructor parameter is used to determine name of individual test cases, see
     * {@link RunAllProofsTestUnit#toString()} for further information.
     *
     * @param proofCollection The file name of the index file which parsed to produce test cases
     * @return The parameters. Each row will be one test case.
     * @throws IOException If an exceptions occurs while reading and parsing the index file
     */

    public static Stream<DynamicTest> data(ProofCollection proofCollection) throws IOException {
        /*
         * Create list of constructor parameters that will be returned by this method. Suitable
         * constructor is automatically determined by JUnit.
         */
        List<RunAllProofsTestUnit> units = proofCollection.createRunAllProofsTestUnits();
        return units.stream().map(it -> DynamicTest.dynamicTest(it.getTestName(), () -> {
            /*
             * Tests each file defined by the instance variables. The tests steps are described in
             * the constructor of this class.
             */
            TestResult report = it.runTest();
            Assertions.assertTrue(report.success, report.message);
        }));
    }

    /**
     * Uses {@link ProofCollectionParser} to parse the given file and returns a parse result that is
     * received from main parser entry point.
     */
    public static ProofCollection parseIndexFile(final String index) throws IOException {
        var errorReporter = new SyntaxErrorReporter(RunAllProofsTest.class);
        var lexer = new ProofCollectionLexer(CharStreams.fromFileName(index));
        lexer.removeErrorListeners();
        lexer.addErrorListener(errorReporter);
        var parser = new ProofCollectionParser(new org.antlr.v4.runtime.CommonTokenStream(lexer));
        parser.removeErrorListeners();
        parser.addErrorListener(errorReporter);
        var ctx = parser.parserEntryPoint();
        errorReporter.throwException();
        var builder = new ProofCollectionBuilder();
        return (ProofCollection) ctx.accept(builder);
    }
}

class ProofCollectionBuilder extends ProofCollectionBaseVisitor<Object> {
    private ProofCollectionSettings currentSettings;

    @Override
    public Object visitParserEntryPoint(ProofCollectionParser.ParserEntryPointContext ctx) {
        var settings = parseSettings(ctx.settingAssignment());
        currentSettings = new ProofCollectionSettings(ctx.start.getTokenSource().getSourceName(), settings, new Date());
        var current = new ProofCollection(currentSettings);
        ctx.group().forEach(it -> current.add((ProofCollectionUnit) it.accept(this)));
        ctx.testFile().forEach(it -> current.add(new SingletonProofCollectionUnit((TestFile) it.accept(this), currentSettings)));
        return current;
    }

    @Override
    public Object visitGroup(ProofCollectionParser.GroupContext ctx) {
        var settings = parseSettings(ctx.settingAssignment());
        var oldSettings = currentSettings;
        currentSettings = new ProofCollectionSettings(oldSettings, settings);
        List<TestFile> files = ctx.testFile().stream().map(it -> (TestFile) it.accept(this)).collect(Collectors.toList());
        var group = new GroupedProofCollectionUnit(ctx.nameToken.getText(), currentSettings, files);
        currentSettings = oldSettings;
        return group;
    }

    @Override
    public Object visitTestFile(ProofCollectionParser.TestFileContext ctx) {
        TestProperty testProperty = null;
        if (ctx.PROVABLE() != null)
            testProperty = TestProperty.PROVABLE;
        if (ctx.NOTPROVABLE() != null) testProperty = TestProperty.NOTPROVABLE;
        if (ctx.LOADABLE() != null)
            testProperty = TestProperty.LOADABLE;
        if (ctx.NOTLOADABLE() != null)
            testProperty = TestProperty.NOTLOADABLE;
        if (testProperty == null)
            throw new IllegalStateException("Parser should have assigned a value other that null to variable testProperty at this point.");
        var path = (String) ctx.path.accept(this);
        return TestFile.createInstance(testProperty, path, currentSettings);
    }

    @Override
    public Object visitValueDeclaration(ProofCollectionParser.ValueDeclarationContext ctx) {
        var value = ctx.getText();
        if (ctx.QuotedString() != null)
            return value.substring(1, value.length() - 1);
        return value;
    }

    private List<Pair<String, String>> parseSettings(List<ProofCollectionParser.SettingAssignmentContext> settingAssignment) {
        return settingAssignment.stream().map(it ->
                new Pair<>(it.k.getText(), (String) it.v.accept(this))
        ).collect(Collectors.toList());
    }
}
