package de.tud.cs.se.ds.secompile.cli;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
public class Main {
    private static final String INFO_STRING =
              "==========================================\n"
            + "        This is pSEC v0.1 \"Alfred\"\n"
            + " prototypical Symbolic Execution Compiler\n"
            + "Better compilation with Symbolic Execution\n"
            + "==========================================\n\n";

    /**
     * TODO
     * 
     * @param args
     */
    public static void main(String[] args) {
        Options options = new Options();

        Option helpOpt = Option.builder("h").longOpt("help")
                .desc("Display help (this text) and terminate").required(false)
                .build();

        options.addOption(helpOpt);

        CommandLineParser parser = new DefaultParser();
        try {
            // parse the command line arguments
            CommandLine line = parser.parse(options, args);

            if (line.getArgList().size() < 1 || line.hasOption("h")) {
                printHelp(options);
                System.exit(0);
            }

            String inputFile = line.getArgList().get(0);
            // TODO
        }
        catch (ParseException exp) {
            printHelp(options);
            System.exit(0);
        }
    }

    private static void printHelp(Options options) {
        System.out.println(INFO_STRING);
        HelpFormatter helpFormatter = new HelpFormatter();
        helpFormatter.printHelp("java -jar pSEC.jar [input file]", options);
    }

}