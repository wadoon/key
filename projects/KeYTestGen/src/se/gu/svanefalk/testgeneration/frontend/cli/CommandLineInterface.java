package se.gu.svanefalk.testgeneration.frontend.cli;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import se.gu.svanefalk.testgeneration.backend.IFrameworkConverter;
import se.gu.svanefalk.testgeneration.backend.TestGenerator;
import se.gu.svanefalk.testgeneration.core.codecoverage.ICodeCoverageParser;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterDescription;

/**
 * Provides a CLI interface for KeYTestGen2.
 * 
 * @author christopher
 */
public final class CommandLineInterface {

    private static class CommandLineInterfaceWorker {

        private static CLIResources cliResources = CLIResources.getInstance();

        /**
         * Hook to KeYTestGen2 itself.
         */
        private static TestGenerator testGenerator = TestGenerator.getInstance();

        /**
         * Prints version and copyright information.
         */
        private static void printAbout() {

            System.out.println("\nKeYTestGen version 2.0\n\n"
                    + "KeYTestGen2 is part of the KeY project, a system for integrated, deductive\n"
                    + "software design. For more info, please visit: <www.key-project.org>\n\n"
                    + "Copyright (C) 2013 Christopher Svanefalk\n"
                    + "This program is free software: you can redistribute it and/or modify\n"
                    + "it under the terms of the GNU General Public License as published by\n"
                    + "the Free Software Foundation, either version 3 of the License, or\n"
                    + "(at your option) any later version.\n\n"
                    + "This program is distributed in the hope that it will be useful,\n"
                    + "but WITHOUT ANY WARRANTY; without even the implied warranty of\n"
                    + "MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n"
                    + "GNU General Public License for more details.\n\n"
                    + "You should have received a copy of the GNU General Public License\n"
                    + "along with this program.  If not, see <http://www.gnu.org/licenses/>.");
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
                System.out.println("\t" + parameter.getNames() + "\t"
                        + parameter.getDescription() + "\n");
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
         * @param args
         *            user provided parameters.
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
                checkAndSetDefaults(parser);

                /*
                 * Generate test suites for each file and each framework
                 * specified by the user, and write them to disc.
                 */
                generateTestCases(parser);

            } catch (final Exception e) {
                System.out.println("Error: " + e.getMessage());
                System.exit(1);
            }
        }

        /**
         * Generate a set of test cases and write them to disc.
         * 
         * @param parser
         */
        private void generateTestCases(CommandParser parser) {

            ICodeCoverageParser coverageParser = cliResources.getCodeCoverageParser(parser.getCoverage());

            for (String file : parser.getFiles()) {

                /*
                 * Create the root folder for the generated test files for this
                 * class.
                 */
                File rootFolder = new File(parser.getOutputDirectory() + "//"
                        + file);
                rootFolder.mkdir();

                for (String framework : parser.getTestFrameworks()) {

                    IFrameworkConverter frameworkConverter = cliResources.getFrameworkConverter(framework);
                    generateTestCases(file, coverageParser, frameworkConverter,
                            parser.getMethods());
                }
            }
        }

        private void generateTestCases(String file,
                ICodeCoverageParser coverageParser,
                IFrameworkConverter frameworkConverter, List<String> methods) {

            List<String> userMethods = new LinkedList<>();
            List<String> methodQualifiers = new LinkedList<>();
            for (String method : methods) {

                if (method.equals("all") || method.equals("public")
                        || method.equals("protected")
                        || method.equals("private") || method.equals("native")) {

                    methodQualifiers.add(method);
                }

                else {
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

        }

        /**
         * Setup default values which are not currently handled by the parser.
         * 
         * @param parser
         */
        private static void checkAndSetDefaults(CommandParser parser) {

            /*
             * Setup default method selection.
             */
            if (parser.getMethods().isEmpty()) {
                parser.getMethods().add("all");
            }

            /*
             * Setup default framework selection.
             */
            if (parser.getMethods().isEmpty()) {
                parser.getTestFrameworks().add("junit4");
            }
        }
    }

    public void execute(String[] args) {

        /*
         * Create a new worker and chop away.
         */
        new CommandLineInterfaceWorker().execute(args);
    }

    public static void main(final String[] args) {

        /*
         * Default output for no-args invocations.
         */
        if (args.length == 0) {
            System.out.println("No arguments specified. Type -h or --help for usage instructions");
            System.exit(0);
        }

        /*
         * Create a new worker and chop away.
         */
        new CommandLineInterfaceWorker().execute(args);
    }
}