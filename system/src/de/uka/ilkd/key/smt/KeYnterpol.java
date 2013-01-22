package de.uka.ilkd.key.smt;

import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.Scanner;
import java.util.concurrent.locks.ReentrantLock;

import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.SMTSolver.SolverState;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.taclettranslation.assumptions.TacletSetTranslation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.SMTInterface;

/**
 * Instances of this class represent, to KeY, an SMT solver running natively
 * with KeY itself (as opposed to external, possibly non-Java solvers such as
 * those represented by ExternalSMTSolverImplementation).
 * 
 * @author christopher
 */
public class KeYnterpol extends AbstractSMTSolver {

    private Collection<Throwable> exceptionsForTacletTranslation = new LinkedList<Throwable>();

    public KeYnterpol(SMTProblem problem, SolverListener listener,
            Services services, SolverType myType) {

        super(myType);
        this.problem = problem;
        this.listener = listener;
        this.services = services;
    }

    /**
     * The main entry point for this process. Sets
     */
    @Override
    public void run() {

        /*
         * Step one: flag the solver as running and notify listeners about this.
         */
        solverState = SolverState.Running;
        listener.processStarted(this, problem);

        /*
         * Second, translate the problem into a solver readable format
         * (depending on which scripting language is used by the particular
         * solver.
         */
        String commands[];
        try {
            commands = translateToCommand(problem.getTerm());
        } catch (Throwable e) {
            interruptionOccurred(e);
            listener.processInterrupted(this, problem, e);
            setSolverState(SolverState.Stopped);
            solverTimeout.cancel();
            return;
        }

        /*
         * TODO: rather than starting an external process, use the native SMT
         * solver instead.
         */
        try {

            /*
             * Pass the problem to the SMT solver
             */
            String response = SMTInterface.INSTANCE
                    .startMessageBasedSession(type.modifyProblem(problemString));

            /*
             * Extract the model portion of the result
             */
            solverCommunication.addMessage(getModel(response));
            
            /*
             * Set the response of the solving process
             */
            solverCommunication.setFinalResult(parseResult(response));


            int x;

        } catch (Throwable e) {
            interruptionOccurred(e);
        } finally {
            solverTimeout.cancel();
            setSolverState(SolverState.Stopped);
            listener.processStopped(this, problem);
        }
    }

    private String getModel(String resultString) {

        Scanner scanner = new Scanner(resultString);
        String model = "";

        while (scanner.hasNext() && scanner.findInLine("model") == null) {
            scanner.nextLine();
        }

        while (scanner.hasNext()) {
            model += scanner.nextLine();
        }

        return model;
    }

    private SMTSolverResult parseResult(String resultString) {

        Scanner scanner = new Scanner(resultString);

        while (scanner.hasNext()) {

            if (scanner.findInLine("sat") != null) {
                return SMTSolverResult.createInvalidResult("satisfiable");
            } else if (scanner.findInLine("unsat") != null) {
                return SMTSolverResult.createValidResult("unsatisfiable");
            }

            scanner.nextLine();
        }

        scanner.close();
        return SMTSolverResult.createUnknownResult("unknown");
    }
}