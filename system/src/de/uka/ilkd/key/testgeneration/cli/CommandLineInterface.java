package de.uka.ilkd.key.testgeneration.cli;

import java.util.ArrayList;
import java.util.List;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterDescription;
import com.sun.xml.internal.stream.writers.WriterUtility;

/**
 * Provides a CLI interface for KeYTestGen2
 * 
 * @author christopher
 */
public final class CommandLineInterface {

    public static void main(String[] args) {

        /*
         * Setup the parser
         */
        CommandParser parser = new CommandParser();
        JCommander processor = new JCommander(parser);
        processor.setProgramName("ktg");

        /*
         * Default output for no-args invocations
         */
        if (args.length == 0) {
            printUsage(processor);
            System.exit(0);
        }

        /*
         * Parse and validate the input
         */
        try {
            processor.parse(args);
        }
        catch (Exception e) {
            System.out.println("Error: " + e.getMessage());
            System.exit(1);
        }

        /*
         * Print help if the user requested this
         */
        if(parser.isHelpFlagSet()) {
            printUsage(processor);
            System.exit(0);
        }
        
        /*
         * Print about info if the user requested this
         */
        if(parser.isAboutFlagSet()) {
            printAbout();
            System.exit(0);
        }
        
        /*
         * If input passed validation, extract relevant values and proceed with test case
         * generation.
         */
        for (String string : parser.getFiles()) {
            System.out.println(string);
        }
    }

    /**
     * Prints usage information for the tool
     * 
     * @param processor
     */
    private static void printUsage(JCommander processor) {

        System.out.println("Usage: ktg [options] [Java source file]");
        System.out.println("\nOptions:");

        for (ParameterDescription string : processor.getParameters()) {
            System.out.println("\t" + string.getNames() + "\t" + string.getDescription());

        }
    }

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