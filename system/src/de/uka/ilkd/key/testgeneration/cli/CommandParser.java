package de.uka.ilkd.key.testgeneration.cli;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
     * Select which Java files to use as a basis for test case generation.
     */
    @Parameter(description = "files", validateWith = JavaFileValidator.class, converter = JavaFileConverter.class)
    private List<File> files = new ArrayList<File>();

    /**
     * Select top-level output directory for the generated test suite(s).
     * Default is the current directory at the time o invocation.
     */
    @Parameter(names = { "-o", "--output" }, description = "target output directory for generated test suites.\n"
            + INDENT + "default: current folder (.))", arity = 1)
    private String outputDirectory = ".";

    /**
     * Select which test framework(s) to generate test cases for. Multiple
     * selections are possible per session, in which case a separate output
     * folder will be generated for each framework. Default is JUnit4.
     */
    @Parameter(names = { "-f", "--framework" }, description = "the test frameworks to use.\n"
            + INDENT
            + "Parameters:\n"
            + INDENT
            + "[framework]\t specify framework to use\n"
            + INDENT
            + "legal frameworks: junit3, junit4")
    private Set<String> testFrameworks = new HashSet<String>();

    /**
     * Select what methods to generate test cases for. This can either be done
     * on a categorical basis (i.e. all, public, private, protected and/or
     * native) or on a specific basis. Both ways can be combined in order to
     * customize method coverage.
     */
    @Parameter(names = { "-m", "--methods" }, description = "what methods should be included in the test suite.\n"
            + INDENT
            + "Parameters:\n"
            + INDENT
            + "all\t\tinclude all user defined methods (default)\n"
            + INDENT
            + "public\t\tinclude all public methods\n"
            + INDENT
            + "private\t\tinclude all private methods\n"
            + INDENT
            + "protected\tinclude all protected methods\n"
            + INDENT
            + "native\t\tinclude methods declared in Java.lang.Object (not recommended)\n"
            + INDENT
            + "[method name]\tspecify methods to include (by identifier)")
    List<String> methods = new ArrayList<String>();

    /**
     * Select the degree of code coverage to guarantee. Only one option per
     * session is legal. Default is standard statement coverage.
     */
    @Parameter(names = { "-c", "--coverage" }, arity = 1, description = "target degree of code coverage for each method.\n"
            + INDENT
            + "Parameters (only one per session):\n"
            + INDENT
            + "statement\tstatement coverage (default)\n"
            + INDENT
            + "branch\t\tbranch coverage\n"
            + INDENT
            + "path\t\tpath coverage\n"
            + INDENT
            + "condition\tcondition coverage\n"
            + INDENT
            + "decision\tdecision coverage\n"
            + INDENT
            + "mcdc\t\tmodified condition/decision coverage")
    List<String> coverageCriteria = new ArrayList<String>();

    /**
     * Flag to decide if usage help should be shown.
     */
    @Parameter(names = { "-h", "--help" }, description = "displays usage help")
    private boolean help;

    /**
     * Set to enable verbose mode.
     */
    @Parameter(names = { "-v", "--verbose" }, description = "enable verbose output")
    private boolean verbose;

    /**
     * Set to display about information.
     */
    @Parameter(names = { "-a", "--about" }, description = "show version and copyright information")
    private boolean about;

    /**
     * @return the files
     */
    public List<File> getFiles() {

        return files;
    }

    /**
     * @return the outputDirectory
     */
    public String getOutputDirectory() {

        return outputDirectory;
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

        return help;
    }

    /**
     * @return the value of the about flag
     */
    public boolean isAboutFlagSet() {

        return about;
    }

    /**
     * @return the indent
     */
    public static String getIndent() {

        return INDENT;
    }

    /**
     * @return the testFrameworks
     */
    public Set<String> getTestFrameworks() {

        return testFrameworks;
    }

    /**
     * @return the methods
     */
    public List<String> getMethods() {

        return methods;
    }
}