package se.gu.svanefalk.testgeneration.frontend.cli;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterDescription;

/**
 * Provides a CLI interface for KeYTestGen2.
 * 
 * @author christopher
 */
public final class CommandLineInterface {

    private static class CommandLineInterfaceWorker {

        /**
         * The {@link XMLTestCaseGenerator} to use for the session serviced by
         * this worker.
         */
        // private XMLTestCaseGenerator testCaseGenerator = null;

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
                 * TODO: method selection needs to be implemented.
                 */
                if (!parser.getMethods().isEmpty()) {
                    System.out.println("Warning: method selection not implemented yet");
                }

                /*
                 * Generate test suites for each file and each framework
                 * specified by the user, and write them to disc.
                 */
                for (final String framework : parser.getTestFrameworks()) {
                    generateTestCases(framework, parser.getFiles());
                }
            } catch (final Exception e) {
                System.out.println("Error: " + e.getMessage());
                System.exit(1);
            }
        }

        /**
         * Create the test cases and write them to an output directory on disc.
         * 
         * @param framework
         *            the framework for which tio
         * @param files
         *            the files to use
         * @throws IOException
         */
        private void generateTestCases(final String framework,
                final List<File> files) throws IOException {

            CLIResources.INSTANCE.getFrameworkParser(framework);

            /*
             * Create an output folder for the framework files, and write the
             * generated test suite to it..
             */
            final File directory = new File(framework);
            directory.mkdir();
            for (final File file : files) {

                final String testSuite = null;
                // testCaseGenerator.generateTestCases(testCaseParser, file,
                // true);

                final File output = new File(framework + "\\" + file.getName());
                output.createNewFile();

                final FileWriter fileWriter = new FileWriter(
                        output.getAbsoluteFile());
                final BufferedWriter bufferedWriter = new BufferedWriter(
                        fileWriter);
                try {
                    bufferedWriter.write(testSuite);
                } finally {
                    bufferedWriter.close();
                }
            }
        }
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