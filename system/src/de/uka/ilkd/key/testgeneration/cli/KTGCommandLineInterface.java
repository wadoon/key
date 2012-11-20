package de.uka.ilkd.key.testgeneration.cli;

import java.util.LinkedList;
import java.util.Queue;

import de.uka.ilkd.key.testgeneration.TestCaseGenerator;
import de.uka.ilkd.key.testgeneration.TestGeneratorException;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.xml.XMLGeneratorException;

/**
 * Provides a CLI interface for KeYTestGen2
 * 
 * @author christopher
 */
public final class KTGCommandLineInterface {

    private final static LinkedList<String> validOptions = new LinkedList<String>();
    static {
        validOptions.add("-b");
        validOptions.add("--batch");
        validOptions.add("-f");
        validOptions.add("--framework");
    }

    private static final String INDENT = "  ";

    /**
     * Directory where generated test cases should be written. Defaults to the local folder.
     */
    private static String outputDirectory = ".";

    /**
     * Framework for which to generate test cases, defaults to JUnit4.
     */
    private static String targetFramework = "junit";

    /**
     * @param args
     * @throws XMLGeneratorException 
     * @throws ModelGeneratorException 
     * @throws TestGeneratorException 
     */
    public static void main(String[] args) throws ModelGeneratorException, XMLGeneratorException, TestGeneratorException {

        if (args.length==0) {
            printHelp();
            System.exit(0);
        } 
        
        String source = args[0];
        System.out.println(source);
        String method = args[1];
        System.out.println(method);
        
        TestCaseGenerator testCaseGenerator = TestCaseGenerator.getDefaultInstance();
        System.out.println(testCaseGenerator.generateTestCase(source, method));
        
        /*
        Queue<String> argumentQueue = new LinkedList<String>();
        for(String argument : args) {
            argumentQueue.add(argument.trim());
        }
        
        parseArgs(argumentQueue);
        printAbout();
        */
    }

    private static void parseArgs(Queue<String> argumentQueue) {

        if (argumentQueue.size() == 1) {
            String argument = argumentQueue.poll();
            if (argument.equals("-v") || argument.equals("--version")) {
                printAbout();
                return;
            }
        }

        while (!argumentQueue.isEmpty()) {
            
            String nextArgument = argumentQueue.poll();
            if(isOption(nextArgument)) {

            }

        }
    }

    private static boolean isOption(String argument) {
        return  validOptions.contains(argument);
    }

    private static void printAbout() {

        System.out.println("\nKeYTestGen2 version 0.1 \n\n"
                + "KeYTestGen2 is part of the KeY project, a system for integrated, deductive\n"
                + "software design. For more info, please visit: www.key-project.org\n\n"
                + "Copyright (C) 2012  Christopher Svanefalk\n"
                + "This is free software, and you are welcome to redistribute it, under the\n"
                + "terms of the GNU General Public License, version 2.0 or later. See the\n"
                + "GPL for more details\n\n"
                + "This software is distributed in the hope that it will be (very!) useful,\n"
                + "however, WITHOUT ANY WARRANTIES WHATSOEVER. Please see the GPL\n"
                + "for a full disclaimer");
    }

    private static void printHelp() {

        System.out.println("Usage: \n" + INDENT + "ktg2 [options]  source | directory \n");

    }

    private static void printOptions() {

        System.out.println("Options: \n "
                + INDENT
                + "-o, --output-dir \t directory to put the generated test cases \n"
                + INDENT
                + "-b, --batch  directory \t create test cases for all sources in directory");
    }

    private static void printFrameWorks() {

    }
}