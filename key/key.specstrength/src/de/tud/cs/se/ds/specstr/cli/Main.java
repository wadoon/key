// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.tud.cs.se.ds.specstr.cli;

import java.io.*;
import java.util.Optional;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import de.tud.cs.se.ds.specstr.analyzer.Analyzer;
import de.tud.cs.se.ds.specstr.gui.AnalyzerGUIDialog;
import javafx.application.Application;

/**
 * Main class for CLI access.
 *
 * @author Dominic Steinhoefel
 */
public final class Main {

    /**
     * The {@link Logger} for this class.
     */
    private static final Logger LOGGER = LogManager.getFormatterLogger();

    /**
     * The information {@link String} for the help output to the command line.
     */
    private static final String INFO_STRING =
    // @formatter:off
              "===========================================\n"
            + "            This is  SpecStr v0.1          \n"
            + "a tool for assessing the strength of formal\n"
            + "  specifications using symbolic execution  \n"
            + "===========================================\n\n";
            // @formatter:on

    /**
     * This is a utility class, the constructor is hidden.
     */
    private Main() {
        // Hidden constructor -- utility class
    }

    /**
     * The main method for running Alfred from command line.
     *
     * @param args
     *            Command line options; run with -h flag for obtaining
     *            information about available options.
     */
    public static void main(String[] args) {
        Options options = new Options();

        Option guiOpt = Option.builder("g").longOpt("gui")
                .desc("Open the Graphical User Interface").required(false)
                .build();

        Option outFileOpt = Option.builder("o").longOpt("out-file")
                .desc("Save output to this file").hasArg().required(false)
                .build();

        Option outFileProofOpt = Option.builder("p").longOpt("proof-out-file")
                .desc("Save proof to this file").hasArg().required(false)
                .build();

        Option helpOpt = Option.builder("h").longOpt("help")
                .desc("Display help (this text) and terminate").required(false)
                .build();

        options.addOption(guiOpt);
        options.addOption(outFileOpt);
        options.addOption(outFileProofOpt);
        options.addOption(helpOpt);

        CommandLineParser parser = new DefaultParser();
        try {
            // parse the command line arguments
            CommandLine line = parser.parse(options, args);

            if ((line.getArgList().size() < 2 && !line.hasOption("g"))
                    || line.hasOption("h")) {
                printHelp(options);
                System.exit(0);
            }

            if (line.hasOption("g")) {
                Application.launch(AnalyzerGUIDialog.class, args);
                return;
            }

            String inputFileName = line.getArgList().get(0);
            File inputFile = new File(inputFileName);
            String theMethod = line.getArgList().get(1);

            if (!inputFileName.endsWith(".java") || !inputFile.exists()
                    || !inputFile.isFile()) {
                System.out.println(
                        "Invalid file name or not existing file: "
                                + inputFileName);
                System.out.println("Please supply an existing Java file.\n");
                printHelp(options);
            }

            Optional<File> outProof = line.hasOption(outFileProofOpt.getOpt())
                    ? Optional.of(
                            new File(line
                                    .getOptionValue(outFileProofOpt.getOpt())))
                    : Optional.empty();

            Analyzer analyzer = new Analyzer(inputFile, theMethod, outProof);
            Analyzer.AnalyzerResult result = analyzer.analyze();

            PrintStream ps = null;
            if (line.hasOption(outFileOpt.getOpt())) {
                File file = new File(line.getOptionValue(outFileOpt.getOpt()));
                try {
                    ps = new PrintStream(new FileOutputStream(file));
                }
                catch (FileNotFoundException e) {
                    LOGGER.error("Could not open file %s", file.getName());
                }
            }

            if (ps == null) {
                ps = System.out;
            }

            Analyzer.printResults(result, ps);

            System.exit(0);
        }
        catch (ParseException exp) {
            printHelp(options);
            System.exit(0);
        }
        catch (RuntimeException e) {
            ByteArrayOutputStream baos = new ByteArrayOutputStream();
            e.printStackTrace(new PrintStream(baos));
            LOGGER.error(
                    "Problem occurred during the analysis:\n%s\n\nStack Trace:\n%s",
                    e.getMessage(), baos.toString());
        }

        System.exit(1);
    }

    /**
     * Prints a standard help line.
     *
     * @param options
     *            Command line options supplied.
     */
    private static void printHelp(Options options) {
         System.out.println(INFO_STRING);
        HelpFormatter helpFormatter = new HelpFormatter();

        helpFormatter.printHelp(String.format(
                "java -cp KeY.jar de.tud.cs.se.ds.specstr.cli.Main\t%s\t%s",
                "[input Java file]", "[fully qualified method name]"),
                "", options, "\nFully qualified method names:\n\t"
                        + "<fully qualified type name>::<method name>(<arg decl>)<return type decl>"
                        + "\n\t<arg decl> is according to the field descriptors "
                        + "in the JVM specification, for instance \"[ILjava.lang.Object;B\" "
                        + "for an integer array, an Object and a boolean");
    }

}
