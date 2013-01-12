package de.uka.ilkd.key.testgeneration.cli;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterDescription;

/**
 * Instances of this class are used in order to parse command line invocations of KeyTestGen2, both
 * checking syntactical correctness and extracting user supplied data,
 * 
 * @author christopher
 */
public class CommandParser {

    /**
     * The Java files to be processed
     */
    @Parameter(description = "files", validateWith = JavaFileValidator.class)
    private List<String> files = new ArrayList<String>();

    /**
     * The output directory
     */
    @Parameter(names = { "-o", "--output" }, description = "the output directory for generated test suites", arity = 1)
    private String outputDirectory = ".";

    /**
     * The test framework(s) to generate test cases for.
     */
    @Parameter(names = { "-f", "--framework" }, description = "the test frameworks to use.\n\t\tlegal frameworks: [junit]")
    private Set<String> testFrameworks = new HashSet<String>();

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
    public List<String> getFiles() {

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
}