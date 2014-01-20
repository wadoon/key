package com.csvanefalk.keytestgen.frontend.cli;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterDescription;
import com.csvanefalk.keytestgen.backend.IFrameworkConverter;
import com.csvanefalk.keytestgen.backend.ITestSuite;
import com.csvanefalk.keytestgen.backend.TestGenerator;
import com.csvanefalk.keytestgen.backend.TestGeneratorException;
import com.csvanefalk.keytestgen.core.codecoverage.ICodeCoverageParser;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

/**
 * Provides a CLI interface for KeYTestGen2.
 *
 * @author christopher
 */
public final class CommandLineInterface {

    /**
     * Worker class to service public invocations to the CLI.
     *
     * @author christopher
     */
    private static class CommandLineInterfaceWorker {

        private static CLIResources cliResources = CLIResources.getInstance();

        /**
         * Hook to KeYTestGen2 itself.
         */
        private static TestGenerator testGenerator = TestGenerator.getInstance();

        /**
         * Setup default values which are not currently handled by the parser.
         *
         * @param parser
         */
        private static void checkAndSetDefaults(final CommandParser parser) {

            /*
             * Setup default method selection.
             */
            if (parser.getMethods().isEmpty()) {
                parser.getMethods().add("all");
            }

            /*
             * Setup default framework selection.
             */
            if (parser.getTestFrameworks().isEmpty()) {
                parser.getTestFrameworks().add("junit4");
            }
        }

        /**
         * Prints version and copyright information.
         */
        private static void printAbout() {

            System.out
                  .println("\nKeYTestGen version 2.0\n\n" + "KeYTestGen2 is part of the KeY project, a system for integrated, deductive\n" + "software design. For more info, please visit: <www.key-project.org>\n\n" + "Copyright (C) 2013 Christopher Svanefalk\n" + "This program is free software: you can redistribute it and/or modify\n" + "it under the terms of the GNU General Public License as published by\n" + "the Free Software Foundation, either version 3 of the License, or\n" + "(at your option) any later version.\n\n" + "This program is distributed in the hope that it will be useful,\n" + "but WITHOUT ANY WARRANTY; without even the implied warranty of\n" + "MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n" + "GNU General Public License for more details.\n\n" + "You should have received a copy of the GNU General Public License\n" + "along with this program.  If not, see <http://www.gnu.org/licenses/>.");
        }

        /**
         * Prints usage information.
         *
         * @param processor
         */
        private static void printUsage(final JCommander processor) {

            System.out.println("Usage: ktg [options] [Java source file]");
            System.out.println("\nOptions:");

            for (final ParameterDescription parameter : processor.getParameters()) {
                System.out.println("\t" + parameter.getNames() + "\t" + parameter.getDescription() + "\n");
            }
        }

        /**
         * The {@link CommandParser} and {@link JCommander} processor to use for
         * the session serviced by this worker.
         */
        CommandParser parser = new CommandParser();

        JCommander processor = new JCommander(parser);

        /**
         * Initialize session environment.
         */
        public CommandLineInterfaceWorker() {

            try {
                // testCaseGenerator =
                // XMLTestCaseGenerator.getDefaultInstance();
            } catch (final Exception e) {
                System.out.println("Error: " + e.getMessage());
                System.exit(1);
            }
            processor.setProgramName("ktg");
        }

        /**
         * Executes a single test case generation session based on the user
         * provided parameters.
         *
         * @param args user provided parameters.
         */
        public void execute(final String[] args) {

            /*
             * Default output for no-args invocations
             */
            if (args.length == 0) {
                CommandLineInterfaceWorker.printUsage(processor);
                System.exit(0);
            }

            /*
             * Main parse cycle
             */
            try {

                /*
                 * Parse and validate the input
                 */
                processor.parse(args);

                /*
                 * Print help if the user requested this
                 */
                if (parser.isHelpFlagSet()) {
                    CommandLineInterfaceWorker.printUsage(processor);
                    System.exit(0);
                }

                /*
                 * Print about info if the user requested this
                 */
                if (parser.isAboutFlagSet()) {
                    CommandLineInterfaceWorker.printAbout();
                    System.exit(0);
                }

                /*
                 * TODO: implement verbose mode
                 */
                if (parser.isVerboseFlagSet()) {
                    System.out.println("Warning: verbose mode not implemented");
                    System.exit(0);
                }

                /*
                 * Set default values, if applicable.
                 */
                CommandLineInterfaceWorker.checkAndSetDefaults(parser);

                /*
                 * Generate test suites for each file and each framework
                 * specified by the user, and write them to disc.
                 */
                generateTestCases(parser);

            } catch (final Exception e) {
                e.printStackTrace();
                System.out.println("Error: " + e.getMessage());
                System.exit(1);
            }
        }

        /**
         * Generate a set of test cases and write them to disc.
         *
         * @param parser
         */
        private void generateTestCases(final CommandParser parser) {

            final ICodeCoverageParser coverageParser = CommandLineInterfaceWorker.cliResources.getCodeCoverageParser(
                    parser.getCoverage());

            for (final String sourceFile : parser.getFiles()) {

                /*
                 * Generate the test suites themselves.
                 */
                List<ITestSuite> testSuites = null;
                for (final String framework : parser.getTestFrameworks()) {
                    final IFrameworkConverter frameworkConverter = CommandLineInterfaceWorker.cliResources
                                                                                             .getFrameworkConverter(
                                                                                                     framework);
                    testSuites = generateTestCases(sourceFile, coverageParser, frameworkConverter, parser.getMethods());
                }

                /*
                 * Create the root folder in which we will put all the generated
                 * test cases.
                 */
                final File rootFolder = new File(parser.getOutputDirectory());
                if (!rootFolder.exists()) {
                    rootFolder.mkdirs();
                }

                /*
                 * Write the files to the folder.
                 */
                for (ITestSuite testSuite : testSuites) {

                    try {

                        File testFolder = getTestFolder(rootFolder, testSuite);
                        if (!testFolder.exists()) {
                            testFolder.mkdirs();
                        }

                        File testFile = new File(testFolder, testSuite.getClassName() + ".java");

                        if (!testFile.exists()) {
                            testFile.createNewFile();
                        }

                        BufferedWriter writer = null;

                        writer = new BufferedWriter(new FileWriter(testFile));
                        writer.write(testSuite.getTestSuiteBody());
                        writer.close();

                    } catch (IOException e) {
                        e.printStackTrace();
                    }
                }
            }
        }

        /**
         * Get a handler for the folder to which a given test suite should be
         * written.
         *
         * @param rootFolder
         * @param testSuite
         * @return
         */
        private File getTestFolder(File rootFolder, ITestSuite testSuite) {

            String path = testSuite.getClassName() + File.separator;
            path += "src" + File.separator;
            String javaPackage = testSuite.getPackage();
            if (javaPackage != null) {
                String[] packageElements = javaPackage.split("[.]");
                for (int i = 0; i < packageElements.length; i++) {
                    path += packageElements[i] + File.separator;
                }
            }
            return new File(rootFolder, path);
        }

        /**
         * Generates a set of test suites for the selected methods of the
         * current class.
         *
         * @param file               path to the Java sourcefile
         * @param coverageParser     parser for the coverage criteria selected
         * @param frameworkConverter converter for the selected framework
         * @param methods            the methods to generate test suites for
         * @return the test suites
         */
        private List<ITestSuite> generateTestCases(final String file,
                                                   final ICodeCoverageParser coverageParser,
                                                   final IFrameworkConverter frameworkConverter,
                                                   final List<String> methods) {

            final List<String> userMethods = new LinkedList<String>();
            final List<String> methodQualifiers = new LinkedList<String>();
            for (final String method : methods) {

                if (method.equals("all") || method.equals("public") || method.equals("protected") || method.equals(
                        "private") || method.equals("native")) {

                    methodQualifiers.add(method);
                } else {
                    userMethods.add(method);
                }
            }

            /*
             * Format the argument list to be passed to KeYTestGen2.
             */
            boolean includePublic = false;
            boolean includeProtected = false;
            boolean includePrivate = false;
            boolean includeNative = false;

            if (methodQualifiers.contains("all")) {

                includePublic = includeProtected = includePrivate = true;
            } else {

                if (methodQualifiers.contains("public")) {

                    includePublic = true;
                }

                if (methodQualifiers.contains("protected")) {

                    includeProtected = true;
                }

                if (methodQualifiers.contains("private")) {

                    includePrivate = true;
                }
            }

            // Malin: 622813
            if (methodQualifiers.contains("native")) {

                includeNative = true;
            }

            List<ITestSuite> testCases = null;
            try {

                /*
                 * Get the test suites.
                 */
                testCases = testGenerator.generateTestSuite(file,
                                                            coverageParser,
                                                            frameworkConverter,
                                                            includePublic,
                                                            includeProtected,
                                                            includePrivate,
                                                            includeNative);

            } catch (TestGeneratorException e) {
                e.printStackTrace();
            }

            return testCases;
        }
    }

    /**
     * Main entry point for the CLI frontend.
     *
     * @param args
     */
    public static void main(String[] args) {

        /*
         * Create a new worker and chop away.
         */
        new CommandLineInterfaceWorker().execute(args);
        System.exit(0);
    }
}