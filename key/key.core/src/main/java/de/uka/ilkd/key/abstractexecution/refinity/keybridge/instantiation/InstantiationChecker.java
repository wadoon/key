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
package de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Comparator;
import java.util.stream.Stream;

import javax.xml.bind.JAXBException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.abstractexecution.refinity.keybridge.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

/**
 * @author Dominic Steinhoefel
 */
public class InstantiationChecker {
    private final AEInstantiationModel model;

    public InstantiationChecker(final AEInstantiationModel instModel) throws IOException {
        this.model = instModel;
    }

    ////////////// Public Static Functions ////////////// 

    ////////////// Public Member Functions //////////////

    public ProofResult proveInstantiation(final boolean printOutput) {
        this.printOutput = printOutput;
        /* non-final */ ProofResult result = ProofResult.EMPTY;

        final InstantiationAspectProver[] checkers = new InstantiationAspectProver[] {
                new FrameConditionProver(), //
                new HasToConditionProver(), //
                new FootprintConditionProver(), //
                new TerminationProver(), //
                new ReturnsSpecProver(), //
        };

        for (final InstantiationAspectProver checker : checkers) {
            println(checker.initMessage());
            final ProofResult checkerProofResult = checker.prove(model);
            printIndividualProofResultStats(checkerProofResult, checker.proofObjective());
            result = result.merge(checkerProofResult);
        }

        ///////// Normal Completion Spec

        //TODO

        ///////// Completion Due to Thrown Exception Spec

        //TODO

        ///////// Completion Due to Break Spec

        //TODO

        ///////// Completion Due to Continue Spec

        //TODO

        ///////// NOTE (DS, 2020-07-16): Labeled continue / break omitted, spec case not yet supported.

        ///////// Constraints (assumptions) satisfied

        //TODO

        ///////// Consistent instantiations of APEs w/ same IDs

        //TODO

        return result;
    }

    ////////////// Private Member Functions //////////////

    private void printIndividualProofResultStats(final ProofResult proofResult,
            String proofObjective) {
        if (printOutput) {
            if (proofResult.isSuccess()) {
                println("Success.");
            } else {
                println("Could not prove " + proofObjective + ".");
            }
        }
    }

    private boolean printOutput = true;

    /**
     * Prints the given string to System.out (w/ newline) if the field
     * {@link #printOutput} is set to true.
     * 
     * @param str The string to (conditionally) print.
     */
    private void println(final String str) {
        if (printOutput) {
            System.out.println(str);
        }
    }

    ////////////// Private Static Functions //////////////

    ////////////// Inner Classes //////////////

    /////////////////// Test Code ///////////////////

    public static void main(String[] args) throws JAXBException, SAXException, IOException,
            ProblemLoaderException, SLTranslationException {
        final Path testFile = Paths.get("/home/dscheurer/key-workspace/GIT/key/key/key.ui/examples/"
                + "abstract_execution/instantiation_checking/SlideStatements/slideStatementsInstP1.aei");
        final AEInstantiationModel instModel = AEInstantiationModel.fromPath(testFile);

        final InstantiationChecker checker = new InstantiationChecker(instModel);
        final ProofResult result = checker.proveInstantiation(true);

        final Path outputDir = Paths.get("output/");
        if (outputDir.toFile().exists()) {
            try (Stream<Path> walk = Files.walk(outputDir)) {
                walk.sorted(Comparator.reverseOrder()).map(Path::toFile).forEach(File::delete);
            }
        }

        result.saveBundlesToDir(outputDir);
        System.out.println("Saved proofs to " + outputDir.toAbsolutePath().toString());
    }
}
