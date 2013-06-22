package se.gu.svanefalk.testgeneration.frontend.cli;

import java.util.ArrayList;
import java.util.List;

import com.beust.jcommander.Parameter;

/**
 * Instances of this class are used in order to parse command line invocations
 * of KeyTestGen2, both checking syntactical correctness and extracting user
 * supplied data,
 * 
 * @author christopher
 */
public class CommandParser {

    private static final String INDENT = "\t\t\t";

    /**
     * @return the indent
     */
    public static String getIndent() {

        return CommandParser.INDENT;
    }

    /**
     * Set to display about information.
     */
    @Parameter(names = { "-a", "--about" }, description = "show version and copyright information")
    private boolean about;

    /**
     * Select the degree of code coverage to guarantee. Only one option per
     * session is legal. Default is standard statement coverage.
     */
    @Parameter(names = { "-c", "--coverage" }, arity = 1, description = "target degree of code coverage for each method.\n"
            + CommandParser.INDENT
            + "Parameters (only one per session):\n"
            + CommandParser.INDENT
            + "statement\tstatement coverage (default)\n"
            + CommandParser.INDENT
            + "branch\t\tbranch coverage\n"
            + CommandParser.INDENT
            + "path\t\tpath coverage\n"
            + CommandParser.INDENT
            + "condition\tcondition coverage\n"
            + CommandParser.INDENT
            + "decision\tdecision coverage\n"
            + CommandParser.INDENT
            + "mcdc\t\tmodified condition/decision coverage")
    private final String coverage = "statement";

    /**
     * Select which Java files to use as a basis for test case generation.
     */
    @Parameter(description = "files", validateWith = JavaFileValidator.class)
    private final List<String> files = new ArrayList<String>();

    /**
     * Flag to decide if usage help should be shown.
     */
    @Parameter(names = { "-h", "--help" }, description = "displays usage help")
    private boolean help;

    /**
     * Select what methods to generate test cases for. This can either be done
     * on a categorical basis (i.e. all, public, private, protected and/or
     * native) or on a specific basis. Both ways can be combined in order to
     * customize method coverage.
     */
    @Parameter(names = { "-m", "--methods" }, echoInput = true, variableArity = true, description = "what methods should be included in the test suite.\n"
            + CommandParser.INDENT
            + "Parameters:\n"
            + CommandParser.INDENT
            + "all\t\tinclude all user defined methods (default)\n"
            + CommandParser.INDENT
            + "public\t\tinclude all public methods\n"
            + CommandParser.INDENT
            + "private\t\tinclude all private methods\n"
            + CommandParser.INDENT
            + "protected\tinclude all protected methods\n"
            + CommandParser.INDENT
            + "native\t\tinclude methods declared in Java.lang.Object (not recommended)\n"
            + CommandParser.INDENT
            + "[method name]\tspecify methods to include (by identifier)")
    private final List<String> methods = new ArrayList<String>();

    /**
     * Select top-level output directory for the generated test suite(s).
     * Default is the current directory at the time o invocation.
     */
    @Parameter(names = { "-o", "--output" }, description = "target output directory for generated test suites.\n"
            + CommandParser.INDENT + "default: current folder (.))", arity = 1)
    private final String outputDirectory = ".";

    /**
     * Select which test framework(s) to generate test cases for. Multiple
     * selections are possible per session, in which case a separate output
     * folder will be generated for each framework. Default is JUnit4.
     */
    @Parameter(names = { "-fr", "--framework" }, variableArity = true, description = "the test frameworks to use.\n"
            + CommandParser.INDENT
            + "Parameters:\n"
            + CommandParser.INDENT
            + "[framework]\t specify framework to use\n"
            + CommandParser.INDENT
            + "legal frameworks: junit3, junit4")
    private final List<String> testFrameworks = new ArrayList<String>();

    /**
     * Set to enable verbose mode.
     */
    @Parameter(names = { "-v", "--verbose" }, description = "enable verbose output")
    private boolean verbose;

    public String getCoverage() {
        return coverage;
    }

    /**
     * @return the files
     */
    public List<String> getFiles() {

        return files;
    }

    /**
     * @return the methods
     */
    public List<String> getMethods() {

        return methods;
    }

    /**
     * @return the outputDirectory
     */
    public String getOutputDirectory() {

        return outputDirectory;
    }

    /**
     * @return the testFrameworks
     */
    public List<String> getTestFrameworks() {

        return testFrameworks;
    }

    /**
     * @return the value of the about flag
     */
    public boolean isAboutFlagSet() {

        return about;
    }

    /**
     * @return the value of the help flag
     */
    public boolean isHelpFlagSet() {

        return help;
    }

    /**
     * @return the value of the verbose flag
     */
    public boolean isVerboseFlagSet() {

        return verbose;
    }
}