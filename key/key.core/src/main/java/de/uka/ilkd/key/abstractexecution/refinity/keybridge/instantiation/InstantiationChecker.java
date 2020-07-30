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
import java.util.Arrays;
import java.util.Comparator;
import java.util.function.Supplier;
import java.util.stream.Stream;

import javax.xml.bind.JAXBException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.prover.AEConstraintsProver;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.prover.InstantiationAspectProver;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.resultobjects.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

/**
 * @author Dominic Steinhoefel
 */
public class InstantiationChecker {
    private final AEInstantiationModel model;
    /* non-final */ ProofResult result;

    public InstantiationChecker(final AEInstantiationModel instModel) throws IOException {
        this.model = instModel;
    }

    ////////////// Public Static Functions ////////////// 

    ////////////// Public Member Functions //////////////

    /**
     * Tries to prove the instantiation correct with separate proof obligations for
     * all aspects.
     * 
     * @param printOutput true <=> Prints some information about the current state
     * to the console, including information about successful and/or failed proofs.
     * @param parallel true <=> Aspects should be proven in parallel. Degree of
     * parallelism is unfortunately limited, since the RECODER framework cannot run
     * in parallel due to the use of static fields (see comment regarding
     * synchronized statement in {@link ProblemInitializer#prepare(EnvInput)}
     * @return A combined {@link ProofResult} for all of the aspect proofs.
     */
    public ProofResult proveInstantiation(final boolean printOutput, boolean parallel) {
        this.printOutput = printOutput;
        this.result = ProofResult.EMPTY;

        final Supplier<Profile> profile = () -> parallel ? new JavaProfile()
                : JavaProfile.getDefaultInstance();

        final InstantiationAspectProver[] checkers = new InstantiationAspectProver[] {
//                new FrameConditionProver(profile.get()), //
//                new HasToConditionProver(profile.get()), //
//                new FootprintConditionProver(profile.get()), //
//                new NormalCompletionSpecProver(profile.get()), //
//                new TerminationProver(profile.get()), //
//                new ReturnsSpecProver(profile.get()), //
//                new ExcSpecProver(profile.get()), //
//                new BreaksSpecProver(profile.get()), //
//                new ContinuesSpecProver(profile.get()), //
//                new PrecMutualExclusionProver(profile.get()), //
//                new PredFuncInstsFootprintConformanceProver(profile.get()), //
//                new ConsistentInstantiationProver(profile.get()), // unimplemented
                new AEConstraintsProver(profile.get()), // unimplemented
        };

        blParr: {
            if (!parallel) {
                break blParr;
            }

            final Thread[] threads = new Thread[checkers.length];

            int i = 0;
            for (final InstantiationAspectProver checker : checkers) {
                threads[i++] = new Thread(() -> {
                    try {
                        println(checker.initMessage());
                        final ProofResult checkerProofResult = checker.prove(model);
                        printIndividualProofResultStats(checkerProofResult,
                                checker.proofObjective());
                        synchronized (result) {
                            result = result.merge(checkerProofResult);
                        }
                    } catch (Throwable t) {
                        System.err.println("Error occurred: " + t.getMessage());
                        t.printStackTrace();
                    }
                });
            }

            Arrays.stream(threads).forEach(Thread::start);
            Arrays.stream(threads).forEach(t -> {
                try {
                    t.join();
                } catch (InterruptedException e) {
                }
            });
        }

        blSeq: {
            if (parallel) {
                break blSeq;
            }

            for (final InstantiationAspectProver checker : checkers) {
                try {
                    println(checker.initMessage());
                    final ProofResult checkerProofResult = checker.prove(model);
                    printIndividualProofResultStats(checkerProofResult, checker.proofObjective());
                    result = result.merge(checkerProofResult);
                } catch (Throwable t) {
                    System.err.println("Error occurred: " + t.getMessage());
                    t.printStackTrace();
                }
            }
        }

        ///////// 

        // TODO:
        // - Consistent instantiations of APEs w/ same IDs
        // - Constraints (assumptions) satisfied
        
        // [ - NOTE (DS, 2020-07-16): Labeled continue / break omitted, spec case not yet supported. ]

        return result;
    }

    ////////////// Private Member Functions //////////////

    private void printIndividualProofResultStats(final ProofResult proofResult,
            String proofObjective) {
        if (printOutput) {
            if (proofResult.isSuccess()) {
                println("Successfully proved " + proofObjective + ".");
            } else {
                err("Could not prove " + proofObjective + ".");
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

    /**
     * Prints the given string to System.out (w/ newline) if the field
     * {@link #printOutput} is set to true.
     * 
     * @param str The string to (conditionally) print.
     */
    private void err(final String str) {
        if (printOutput) {
            System.err.println(str);
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

        long startTime = System.currentTimeMillis();

        final InstantiationChecker checker = new InstantiationChecker(instModel);
        final ProofResult result = checker.proveInstantiation(true, false);

        long endTime = System.currentTimeMillis();
        double durationSecs = (double) (endTime - startTime) / (double) 1000;
        System.out.println("Duration: " + durationSecs + "s");

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
