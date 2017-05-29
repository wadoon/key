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

import java.io.File;

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
import de.tud.cs.se.ds.specstr.util.Utilities;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class Main {

    private static final Logger logger = LogManager.getFormatterLogger();

    private static final String INFO_STRING =
            // @formatter:off
              "===========================================\n"
            + "            This is  SpecStr v0.1          \n"
            + "a tool for assessing the strength of formal\n"
            + "  specifications using symbolic execution  \n"
            + "===========================================\n\n";
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

        Option helpOpt = Option.builder("h").longOpt("help")
                .desc("Display help (this text) and terminate").required(false)
                .build();

        options.addOption(helpOpt);

        CommandLineParser parser = new DefaultParser();
        try {
            // parse the command line arguments
            CommandLine line = parser.parse(options, args);

            if (line.getArgList().size() < 2 || line.hasOption("h")) {
                printHelp(options);
                System.exit(0);
            }

            String inputFileName = line.getArgList().get(0);
            File inputFile = new File(inputFileName);
            String theMethod = line.getArgList().get(1);

            if (!inputFileName.endsWith(".java") || !inputFile.exists()
                    || !inputFile.isFile()) {
                System.out.println("Invalid file name or not existing file: "
                        + inputFileName);
                System.out.println("Please supply an existing Java file.\n");
                printHelp(options);
            }

            Analyzer analyzer = new Analyzer(inputFile, theMethod);
            Analyzer.AnalyzerResult result = analyzer.analyze();
            
            System.out.printf("Covered %s out of %s facts; Strength: %.2f%%\n",
                    result.numCoveredFacts(), result.numFacts(),
                    100d * ((double) result.numCoveredFacts())
                            / ((double) result.numFacts()));

            // @formatter:off
            System.out.println("\n================\n"
                               + "Uncovered Facts:\n"
                               + "================\n");
            // @formatter:on

            result.getUnCoveredFacts().forEach(f -> {
                System.out.println(f);
                System.out.println();
            });

            System.exit(0);
        } catch (ParseException exp) {
            printHelp(options);
            System.exit(0);
        } catch (ProblemLoaderException e) {
            logger.error("Problem in loading the file to analyze, message:\n%s",
                    e.getMessage());
        } catch (RuntimeException e) {
            logger.error("Problem occurred during the analysis:\n%s",
                    e.getMessage());
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
        helpFormatter.printHelp("java -jar key.specstrength.jar"
                + "\t[input Java file]" + "\t[fully qualified method name]",
                options);
    }

}
