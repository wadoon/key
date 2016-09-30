package de.tud.cs.se.ds.psec.cli;

import java.io.File;
import java.io.IOException;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import de.tud.cs.se.ds.psec.compiler.Compiler;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * The main class for running Alfred from command line.
 *
 * @see #main(String[])
 * @author Dominic Scheurer
 */
public class Main {
    private static final Logger logger = LogManager.getFormatterLogger();

    private static final String INFO_STRING =
            // @formatter:off
              "==========================================\n"
            + "        This is pSEC v0.1 \"Alfred\"      \n"
            + " prototypical Symbolic Execution Compiler \n"
            + "Better Compilation with Symbolic Execution\n"
            + "==========================================\n\n";
            // @formatter:on

    /**
     * The main method for running Alfred from command line.
     * 
     * @param args
     *            Command line options; run with -h flag for obtaining
     *            information about available options.
     */
    public static void main(String[] args) {
        Options options = new Options();

        Option outputDirOpt = Option.builder("o").longOpt("output-dir")
                .desc("The directory to which files should be written").hasArg()
                .required(false).build();

        Option dumpSETOpt = Option.builder("d").longOpt("dump-set")
                .desc("Dump a .proof file containing the KeY SET for each compiled method")
                .required(false).build();

        Option debugOpt = Option.builder("X").longOpt("debug")
                .desc("Print additional bytecode verifier output if compilation fails")
                .required(false).build();

        Option bailAtParseErrorOpt = Option.builder("b")
                .longOpt("bail-at-parser-error")
                .desc("Don't try to recover from syntax errors in the "
                        + "translation taclet definition file. Stop instead.")
                .required(false).build();

        Option helpOpt = Option.builder("h").longOpt("help")
                .desc("Display help (this text) and terminate").required(false)
                .build();

        options.addOption(outputDirOpt);
        options.addOption(dumpSETOpt);
        options.addOption(debugOpt);
        options.addOption(bailAtParseErrorOpt);
        options.addOption(helpOpt);

        CommandLineParser parser = new DefaultParser();
        try {
            // parse the command line arguments
            CommandLine line = parser.parse(options, args);

            if (line.getArgList().size() < 1 || line.hasOption("h")) {
                printHelp(options);
                System.exit(0);
            }

            String inputFileName = line.getArgList().get(0);
            File inputFile = new File(inputFileName);

            if (!inputFileName.endsWith(".java") || !inputFile.exists()
                    || !inputFile.isFile()) {
                System.out.println("Invalid file name or not existing file: "
                        + inputFileName);
                System.out.println("Please supply an existing Java file.\n");
                printHelp(options);
            }

            String outputDir = line.hasOption('o') ? line.getOptionValue('o')
                    : ".";
            if (!outputDir.endsWith("/")) {
                outputDir = outputDir + "/";
            }

            Compiler compiler = new Compiler(inputFile, outputDir,
                    line.hasOption("X"), line.hasOption("d"), line.hasOption('b'));

            compiler.compile();
            
        }
        catch (ParseException exp) {
            printHelp(options);
            System.exit(0);
        }
        catch (IOException e) {
            logger.error("I/O error in reading translation taclets, message:\n%s", e.getMessage());
        }
        catch (ProblemLoaderException e) {
            logger.error("Problem in loading the file to compile, message:\n%s", e.getMessage());
        }
    }

    /**
     * Prints a standard help line for Alfred.
     *
     * @param options
     *            Command line options supplied.
     */
    private static void printHelp(Options options) {
        System.out.println(INFO_STRING);
        HelpFormatter helpFormatter = new HelpFormatter();
        helpFormatter.printHelp("java -jar pSEC.jar [input Java file]",
                options);
    }

}