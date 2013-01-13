package de.uka.ilkd.key.testgeneration.cli;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterDescription;

import de.uka.ilkd.key.testgeneration.TestCaseGenerator;
import de.uka.ilkd.key.testgeneration.xmlparser.ITestCaseParser;

/**
 * Provides a CLI interface for KeYTestGen2.
 * 
 * @author christopher
 */
public final class CommandLineInterface {

    public static void main(String[] args) {

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

    private static class CommandLineInterfaceWorker {

        /**
         * The {@link TestCaseGenerator} to use for the session serviced by this worker.
         */
        private TestCaseGenerator testCaseGenerator = null;

        /**
         * The parser and {@link JCommander} processor to use for the session serviced by this
         * worker.
         */
        CommandParser parser = new CommandParser();
        JCommander processor = new JCommander(parser);

        /**
         * Initialize session environment.
         */
        public CommandLineInterfaceWorker() {

            try {
                testCaseGenerator = TestCaseGenerator.getDefaultInstance();
            }
            catch (Exception e) {
                System.out.println("Error: " + e.getMessage());
                System.exit(1);
            }
            processor.setProgramName("ktg");
        }

        /**
         * Executes a single test case generation session based on the user provided parameters.
         * 
         * @param args
         *            user provided parameters.
         */
        public void execute(String[] args) {

            /*
             * Default output for no-args invocations
             */
            if (args.length == 0) {
                printUsage(processor);
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
                    printUsage(processor);
                    System.exit(0);
                }

                /*
                 * Print about info if the user requested this
                 */
                if (parser.isAboutFlagSet()) {
                    printAbout();
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
                 * Generate test suites for each file and each framework specified by the user, and
                 * write them to disc.
                 */
                for (String framework : parser.getTestFrameworks()) {
                    generateTestCases(framework, parser.getFiles());
                }
            }
            catch (Exception e) {
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
        private void generateTestCases(String framework, List<File> files)
                throws IOException {

            ITestCaseParser<String> testCaseParser =
                    CLIResources.INSTANCE.getFrameworkParser(framework);

            /*
             * Create an output folder for the framework files, and write the generated test suite
             * to it..
             */
            File directory = new File(framework);
            directory.mkdir();
            for (File file : files) {

                String testSuite =
                        testCaseGenerator.generateTestCases(testCaseParser, file, true);

                File output = new File(framework + "\\" + file.getName());
                output.createNewFile();

                FileWriter fileWriter = new FileWriter(output.getAbsoluteFile());
                BufferedWriter bufferedWriter = new BufferedWriter(fileWriter);
                try {
                    bufferedWriter.write(testSuite);
                }
                finally {
                    bufferedWriter.close();
                }
            }
        }

        /**
         * Prints usage information.
         * 
         * @param processor
         */
        private static void printUsage(JCommander processor) {

            System.out.println("Usage: ktg [options] [Java source file]");
            System.out.println("\nOptions:");

            for (ParameterDescription parameter : processor.getParameters()) {
                System.out.println("\t" + parameter.getNames() + "\t"
                        + parameter.getDescription() + "\n");
            }
        }

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
    }
}