package de.uka.ilkd.key.smt;

import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.concurrent.locks.ReentrantLock;

import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.SMTSolver.SolverState;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.taclettranslation.assumptions.TacletSetTranslation;

/**
 * Instances of this class represent, to KeY, an SMT solver running natively with KeY itself (as
 * opposed to external, possibly non-Java solvers such as those represented by
 * ExternalSMTSolverImplementation).
 * 
 * @author christopher
 */
public class EmbeddedSMTSolverImplementation
        extends AbstractSMTSolver {

    private Collection<Throwable> exceptionsForTacletTranslation =
            new LinkedList<Throwable>();

    public EmbeddedSMTSolverImplementation(
            SMTProblem problem,
            SolverListener listener,
            Services services,
            SolverType myType) {

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
         * Second, translate the problem into a solver readable format (depending on which scripting
         * language is used by the particular solver.
         */
        String commands[];
        try {
            commands = translateToCommand(problem.getTerm());
        }
        catch (Throwable e) {
            interruptionOccurred(e);
            listener.processInterrupted(this, problem, e);
            setSolverState(SolverState.Stopped);
            solverTimeout.cancel();
            return;
        }

        /*
         * TODO: rather than starting an external process, use the native SMT solver instead.
         */
        try {
            
        }
        catch (Throwable e) {
            interruptionOccurred(e);
        }
        finally {
            // Close every thing.
            solverTimeout.cancel();
            setSolverState(SolverState.Stopped);
            listener.processStopped(this, problem);
        }
    }
}
