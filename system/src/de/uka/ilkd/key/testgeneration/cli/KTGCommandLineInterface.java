package de.uka.ilkd.key.testgeneration.cli;

/**
 * Provides a CLI interface for KeYTestGen2
 * 
 * @author christopher
 */
public class KTGCommandLineInterface {

    private static final String INDENT = "  ";

    /**
     * @param args
     */
    public static void main(String[] args) {

        parseArgs(args);
    }

    private static void parseArgs(String[] args) {

        if (args.length == 0) {
            printHelp();
            System.exit(0);
        }
    }

    private static void printAbout() {

        System.out.println("KeYTestGen2, version 0.1 \n\n"
                + "KeYTestGen2 is part of the KeY project, a system for \n"
                + "integrated, deductive software design: www.key-project.org");
    }

    private static void printHelp() {

        System.out.println("Usage: \n" + INDENT
                + "ktg2 [options] [framework] source | directory \n");

    }

    private static void printOptions() {

        System.out
                .println("Options: \n "
                        + INDENT
                        + "-o, --output-dir \t directory to put the generated test cases \n"
                        + INDENT
                        + "-b, --batch  directory \t create test cases for all sources in directory");
    }

    private static void printFrameWorks() {

    }
}