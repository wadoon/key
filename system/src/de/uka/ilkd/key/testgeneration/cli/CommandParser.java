package de.uka.ilkd.key.testgeneration.cli;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.beust.jcommander.Parameter;

/**
 * Instances of this class are used in order to parse command line invocations of KeyTestGen2, both
 * checking syntactical correctness and extracting user supplied data,
 * 
 * @author christopher
 */
public class CommandParser {

    private static final String INDENT = "\t\t\t";

    /**
     * The Java files to be processed
     */
    @Parameter(description = "files", validateWith = JavaFileValidator.class, converter = JavaFileConverter.class)
    private List<File> files = new ArrayList<File>();

    /**
     * The output directory
     */
    @Parameter(names = { "-o", "--output" }, description = "target output directory for generated test suites.\n"
            + INDENT + "default: current folder (.))", arity = 1)
    private String outputDirectory = ".";

    /**
     * The test framework(s) to generate test cases for.
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
     * Set to generate test cases also for private methods
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
            + INDENT + "[method name]\tspecify methods to include (by identifier)")
    List<String> methods;

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