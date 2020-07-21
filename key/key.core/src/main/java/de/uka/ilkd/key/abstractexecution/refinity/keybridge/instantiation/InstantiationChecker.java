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
import java.nio.file.Path;
import java.nio.file.Paths;

import javax.xml.bind.JAXBException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.abstractexecution.refinity.keybridge.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.proof.Proof;
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
                new FootprintConditionProver()
        };

        for (final InstantiationAspectProver checker : checkers) {
            println(checker.initMessage());
            final ProofResult checkerProofResult = checker.prove(model);
            printIndividualProofResultStats(checkerProofResult, checker.proofObjective());
            result = result.merge(checkerProofResult);
        }

        ///////// Termination

        ///////// Normal Completion Spec

        ///////// Completion Due to Return Spec

        ///////// Completion Due to Thrown Exception Spec

        ///////// Completion Due to Break Spec

        ///////// Completion Due to Continue Spec

        ///////// NOTE (DS, 2020-07-16): Labeled continue / break omitted, spec case not yet supported.

        ///////// Constraints (assumptions) satisfied

        ///////// Consistent instantiations of APEs w/ same IDs

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
                println("Failed proof(s):");
                proofResult.getProofs().stream().filter(p -> !p.closed()).map(Proof::getProofFile)
                        .map(File::toString).forEach(this::println);
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
//        final Path testFile = Paths.get(
//                "/home/dscheurer/key-workspace/GIT/key/key/key.ui/examples/abstract_execution/SlideStatements/Correct/slideStatements.aer");
//        final AERelationalModel relModel = //
//                AERelationalModel.fromXml(
//                        Files.readAllLines(testFile).stream().collect(Collectors.joining("\n")));
//
//        // There are ASs at lines 19 and 25
//        final AEInstantiationModel instModel = //
//                AEInstantiationModel.fromRelationalModel(relModel, true);
//
//        for (final String newPV : new String[] { "a", "b", "d", "w", "x", "y", "z" }) {
//            instModel.getProgramVariableDeclarations()
//                    .add(new ProgramVariableDeclaration("int", newPV));
//        }
//
//        instModel.addFunctionInstantiation(new FunctionInstantiation(
//                instModel.getAbstractLocationSets().stream()
//                        .filter(decl -> decl.getFuncName().equals("frameA")).findAny().get(),
//                "union(singletonPV(PV(x)), union(singletonPV(PV(y)), singletonPV(PV(z))))"));
//
//        instModel.addFunctionInstantiation(new FunctionInstantiation(
//                instModel.getAbstractLocationSets().stream()
//                        .filter(decl -> decl.getFuncName().equals("footprintA")).findAny().get(),
//                "union(singletonPV(PV(y)), singletonPV(PV(w)))"));
//
//        instModel.addApeInstantiation(new APEInstantiation(19, "x = y++; z = w;"));
//        instModel.addApeInstantiation(new APEInstantiation(25, "a = b + 17; int c = 2*d+a;"));

        final Path testFile = Paths.get("/home/dscheurer/key-workspace/GIT/key/key/key.ui/examples/"
                + "abstract_execution/instantiation_checking/SlideStatements/slideStatementsInstP1.aei");
        final AEInstantiationModel instModel = AEInstantiationModel.fromPath(testFile);

        final InstantiationChecker checker = new InstantiationChecker(instModel);
        checker.proveInstantiation(true);
    }
}
