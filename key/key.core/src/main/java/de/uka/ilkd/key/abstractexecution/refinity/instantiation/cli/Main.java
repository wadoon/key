// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.instantiation.cli;

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.JAXBException;

import org.key_project.util.helper.FindResources;
import org.xml.sax.SAXException;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;

import de.uka.ilkd.key.abstractexecution.refinity.instantiation.InstantiationChecker;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.resultobjects.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.model.relational.AERelationalModel;

/**
 * Main CLI file for proving instantiation models.
 * 
 * @author Dominic Steinhoefel
 */
public class Main {
    private static final String SCHEMA_FILE_PATH = "/de/uka/ilkd/key/refinity/instantiation/schema2.xsd";

    @Parameter
    private List<String> parameters = new ArrayList<>();

    @Parameter(names = "-help", help = true, description = "Print this help message and exit.")
    private boolean help;

    @Parameter(names = { "-file",
            "-input" }, description = "Input file (if neither -help or -printschema are set)")
    private String inputFile = null;

    @Parameter(names = { "-save" }, description = "true to save proofs to output directory")
    private boolean saveProofs = false;

    @Parameter(names = { "-output", "-outputDir" }, description = "Output directory")
    private String outDir = "output/";

    @Parameter(names = { "-verbose" }, description = "Level of verbosity (0, 1, 2, 4)")
    private int verbosity = 1;

    @Parameter(names = {
            "-conv" }, description = "Convert an *.aer model to an *.aei instantiation model")
    private boolean convertAERModel = false;

    @Parameter(names = {
            "-right" }, description = "If -conv is set, this chooses the right program "
                    + "of the relational model for conversion. Omit for the left program.")
    private boolean rightProgram = false;

    @Parameter(names = { "-convout",
            "-outfile" }, description = "If -conv is set, this sets the output file for the *.aei model.")
    private String convOutFile = "output.aei";

    @Parameter(names = {
            "-printschema" }, description = "If set, prints the XML schema for *.aei files and exists.")
    private boolean printSchemaFile = false;

    private void convertRelationalModel(final Path file) {
        if (!AERelationalModel.fileHasAEModelEnding(file.toFile())) {
            System.err.printf("No *.aer file: %s%n", file.getFileName());
            System.exit(1);
            return;
        }

        final AERelationalModel aerModel;
        try {
            aerModel = AERelationalModel.fromPath(file);
        } catch (JAXBException | SAXException | IOException e) {
            System.err.printf("Problem parsing AE Relational Model (%s): %s%n",
                    e.getClass().getName(), e.getMessage());
            System.exit(1);
            return;
        }

        final AEInstantiationModel instModel = //
                AEInstantiationModel.fromRelationalModel(aerModel, !rightProgram);
        final Path outfile = Paths.get(convOutFile);
        try {
            instModel.saveToFile(outfile.toFile());
        } catch (IOException | JAXBException e) {
            System.err.printf("Problem saving AE Instantiation Model (%s): %s%n",
                    e.getClass().getName(), e.getMessage());
            System.exit(1);
            return;
        }
    }

    private void printSchema() {
        try {
            final Path schemaFilePath = FindResources.getResource(SCHEMA_FILE_PATH, Main.class);
            byte[] encoded = Files.readAllBytes(schemaFilePath);
            System.out.println(new String(encoded, StandardCharsets.UTF_8));
        } catch (URISyntaxException | IOException e) {
            System.err.printf("Problem while trying to access schema file resouce (%s): %s%n",
                    e.getClass().getName(), e.getMessage());
            System.exit(1);
            return;
        }
    }

    private void proofInstantiationModel(final Path file) {
        if (!AEInstantiationModel.fileHasAEModelEnding(file.toFile())) {
            System.err.printf("No *.aei file: %s%n", file.getFileName());
            System.exit(1);
            return;
        }

        final AEInstantiationModel instModel;
        try {
            instModel = AEInstantiationModel.fromPath(file);
        } catch (JAXBException | SAXException | IOException e) {
            System.err.printf("Problem parsing AE Instantiation Model (%s): %s%n",
                    e.getClass().getName(), e.getMessage());
            System.exit(1);
            return;
        }

        final ProofResult result;
        try {
            final InstantiationChecker checker = new InstantiationChecker(instModel);
            result = checker.proveInstantiation(verbosity, false);
        } catch (IOException e) {
            System.err.printf("I/O exception when checking correctness of instantiation: %s%n",
                    e.getMessage());
            System.exit(1);
            return;
        }

        if (saveProofs) {
            final Path outputDir = Paths.get(outDir);

            try {
                result.saveBundlesToDir(outputDir);
                System.out.println("Saved proofs to " + outputDir.toAbsolutePath().toString());
            } catch (IOException e) {
                System.err.printf("Problem saving proofs to output directory: %s%n",
                        e.getMessage());
                System.exit(1);
            }
        }
    }

    private void run(final JCommander jcommander) {
        if (help) {
            jcommander.usage();
            System.exit(0);
        }

        if (printSchemaFile) {
            printSchema();
            System.exit(0);
            return;
        }

        if (inputFile == null) {
            System.err.println("You have to specify an input file (-file).");
            jcommander.usage();
            System.exit(1);
            return;
        }

        final Path file = Paths.get(inputFile);

        if (convertAERModel) {
            convertRelationalModel(file);
        } else {
            proofInstantiationModel(file);
        }

        System.exit(0);
    }

    public static void main(String... argv) {
        Main main = new Main();
        final JCommander jcommander = JCommander.newBuilder().addObject(main).build();
        jcommander.parse(argv);
        main.run(jcommander);
    }

}
