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

        // Firstly: Set the state to running and inform the listener.
        solverState = SolverState.Running;
        listener.processStarted(this, problem);

        // Secondly: Translate the given problem
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

    private void setSolverState(SolverState value) {

        try {
            lockStateVariable.lock();
            solverState = value;
        }
        finally { // finally trumps return
            lockStateVariable.unlock();
        }
    }

    @Override
    public String name() {

        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public String getTranslation() {

        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public TacletSetTranslation getTacletTranslation() {

        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public SolverType getType() {

        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public SMTProblem getProblem() {

        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Throwable getException() {

        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public void interrupt(ReasonOfInterruption reasonOfInterruption) {

        // TODO Auto-generated method stub

    }

    @Override
    public long getStartTime() {

        // TODO Auto-generated method stub
        return 0;
    }

    @Override
    public long getTimeout() {

        // TODO Auto-generated method stub
        return 0;
    }

    @Override
    public SolverState getState() {

        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public boolean wasInterrupted() {

        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isRunning() {

        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public ReasonOfInterruption getReasonOfInterruption() {

        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public SMTSolverResult getFinalResult() {

        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public String getSolverOutput() {

        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Collection<Throwable> getExceptionsOfTacletTranslation() {

        // TODO Auto-generated method stub
        return null;
    }

}
