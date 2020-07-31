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
package de.uka.ilkd.key.abstractexecution.refinity.instantiation;

import java.io.IOException;
import java.util.Arrays;
import java.util.function.Supplier;

import de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover.AEConstraintsProver;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover.BreaksSpecProver;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover.ConsistentInstantiationProver;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover.ContinuesSpecProver;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover.ExcSpecProver;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover.FootprintConditionProver;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover.FrameConditionProver;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover.HasToConditionProver;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover.InstantiationAspectProver;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover.NormalCompletionSpecProver;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover.PrecMutualExclusionProver;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover.PredFuncInstsFootprintConformanceProver;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover.ReturnsSpecProver;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.prover.TerminationProver;
import de.uka.ilkd.key.abstractexecution.refinity.instantiation.resultobjects.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.io.EnvInput;

/**
 * @author Dominic Steinhoefel
 */
public class InstantiationChecker {
    private final AEInstantiationModel model;
    /* non-final */ ProofResult result;

    /**
     * Verbosity: 0 for totally silent, 1 for basic status information, 2 for
     * detailed status information, 4 for debug information. Currently, 2/4 are not
     * implemented/considered.
     */
    private int verbosity = 0;

    public InstantiationChecker(final AEInstantiationModel instModel) throws IOException {
        this.model = instModel;
    }

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
    public ProofResult proveInstantiation(final int verbosity, boolean parallel) {
        this.verbosity = verbosity;
        this.result = ProofResult.EMPTY;

        final Supplier<Profile> profile = () -> parallel ? new JavaProfile()
                : JavaProfile.getDefaultInstance();

        final InstantiationAspectProver[] checkers = new InstantiationAspectProver[] {
                new FrameConditionProver(profile.get()), //
                new HasToConditionProver(profile.get()), //
                new FootprintConditionProver(profile.get()), //
                new NormalCompletionSpecProver(profile.get()), //
                new TerminationProver(profile.get()), //
                new ReturnsSpecProver(profile.get()), //
                new ExcSpecProver(profile.get()), //
                new BreaksSpecProver(profile.get()), //
                new ContinuesSpecProver(profile.get()), //
                new PrecMutualExclusionProver(profile.get()), //
                new PredFuncInstsFootprintConformanceProver(profile.get()), //
                new ConsistentInstantiationProver(profile.get()), // unimplemented
                new AEConstraintsProver(profile.get()), //
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

        // [ - NOTE (DS, 2020-07-16): Labeled continue / break omitted, spec case not yet supported. ]

        return result;
    }

    /**
     * Prints the given string to System.out (w/ newline) if the field
     * {@link #printOutput} is set to true.
     * 
     * @param str The string to (conditionally) print.
     */
    private void err(final String str) {
        if (verbosity > 0) {
            System.err.println(str);
        }
    }

    private void printIndividualProofResultStats(final ProofResult proofResult,
            String proofObjective) {
        if (verbosity > 0) {
            if (proofResult.isSuccess()) {
                println("Successfully proved " + proofObjective + ".");
            } else {
                err("Could not prove " + proofObjective + ".");
            }
        }
    }

    /**
     * Prints the given string to System.out (w/ newline) if the field
     * {@link #printOutput} is set to true.
     * 
     * @param str The string to (conditionally) print.
     */
    private void println(final String str) {
        if (verbosity > 0) {
            System.out.println(str);
        }
    }
}
