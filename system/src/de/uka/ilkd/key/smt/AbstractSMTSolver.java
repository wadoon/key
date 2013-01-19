package de.uka.ilkd.key.smt;

import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.concurrent.locks.ReentrantLock;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.taclettranslation.assumptions.TacletSetTranslation;

/**
 * Represents the basis for an {@link SMTSolver} implementation, providing common data and utility
 * methods.
 * 
 * @author christopher
 */
public abstract class AbstractSMTSolver
        implements SMTSolver, Runnable {

    /**
     * The {@link SMTProblem} instance that is associated with this solver.
     */
    protected SMTProblem problem;

    /**
     * The {@link SolverListener} instance associated with this solver, if any.
     */
    protected SolverListener listener;

    /**
     * The services object is stored in order to have the possibility to access it in every method
     */
    protected Services services;

    /**
     * The record of the communication between KeY and the given solver. If everything works fine,
     * it also contains the final result.
     */
    protected SolverCommunication solverCommunication = SolverCommunication.EMPTY;

    /**
     * This lock variable is responsible for the state variable <code>sovlerState</code>
     */
    protected ReentrantLock lockStateVariable = new ReentrantLock();

    /**
     * This lock variable is responsible for the attribute <code>reasonOfInterruption</code>
     */
    protected ReentrantLock lockInterruptionVariable = new ReentrantLock();

    /**
     * The thread that is associated with this solver.
     */
    protected Thread thread;

    /**
     * The timeout that is associated with this solver. Represents the timertask that is started
     * when the solver is started.
     */
    protected SolverTimeout solverTimeout;

    /**
     * In the event that the solver is interrupted in the course of interruption, the reason for
     * such an interruption will be stored in this variable.
     */
    protected ReasonOfInterruption reasonOfInterruption =
            ReasonOfInterruption.NoInterruption;

    /**
     * The current state of the solver.
     */
    protected SolverState solverState = SolverState.Waiting;

    /**
     * The type of the solver.
     */
    protected final SolverType type;

    /**
     * Settings for this particular execution of the SMT solver.
     */
    protected SMTSettings smtSettings;

    /**
     * Stores the translation of the problem that is associated with this solver
     */
    protected String problemString = "NOT YET COMPUTED";

    /** Stores the taclet translation that is associated with this solver. */
    protected TacletSetTranslation tacletTranslation;

    /**
     * If there was an exception while executing the solver it is stored in this attribute
     */
    protected Throwable exception;

    protected Collection<Throwable> exceptionsForTacletTranslation =
            new LinkedList<Throwable>();

    public AbstractSMTSolver(SolverType type) {

        this.type = type;
    }

    protected static String indent(String string) {

        StringBuilder sb = new StringBuilder();
        int indention = 0;

        for (int i = 0; i < string.length(); i++) {
            char c = string.charAt(i);
            switch (c) {
                case '(':
                    sb.append("\n");
                    for (int j = 0; j < indention; j++)
                        sb.append(" ");
                    sb.append("(");
                    indention++;
                    break;
                case ')':
                    indention--;
                    // fall through
                default:
                    sb.append(c);
            }
        }

        return sb.toString();
    }

    protected String[] translateToCommand(Term term)
            throws IllegalFormulaException, IOException {

        SMTTranslator trans = getType().createTranslator(services);
        // instantiateTaclets(trans);

        problemString =
                indent(trans.translateProblem(term, services, smtSettings).toString());

        tacletTranslation = ((AbstractSMTTranslator) trans).getTacletSetTranslation();
        exceptionsForTacletTranslation.addAll(trans.getExceptionsOfTacletTranslation());
        String parameters[] = this.type.getSolverParameters().split(" ");
        String result[] = new String[parameters.length + 1];
        for (int i = 0; i < result.length; i++) {
            result[i] = i == 0 ? type.getSolverCommand() : parameters[i - 1];
        }
        return result;
    }

    public Throwable getException() {

        return isRunning() ? null : exception;
    }

    public SMTProblem getProblem() {

        return isRunning() ? null : problem;
    }

    public void setReasonOfInterruption(ReasonOfInterruption reasonOfInterruption) {

        try {
            lockInterruptionVariable.lock();
            this.reasonOfInterruption = reasonOfInterruption;
        }
        finally {
            lockInterruptionVariable.unlock();
        }
    }

    protected void setReasonOfInterruption(
            ReasonOfInterruption reasonOfInterruption,
            Throwable exc) {

        try {
            lockInterruptionVariable.lock();
            this.reasonOfInterruption = reasonOfInterruption;
            this.exception = exc;
        }
        finally {
            lockInterruptionVariable.unlock();
        }
    }

    protected void interruptionOccurred(Throwable e) {

        ReasonOfInterruption reason = getReasonOfInterruption();
        switch (reason) {
            case Exception:
            case NoInterruption:
                setReasonOfInterruption(ReasonOfInterruption.Exception, e);
                listener.processInterrupted(this, problem, e);
                break;
            case Timeout:
                listener.processTimeout(this, problem);
                break;
            case User:
                listener.processUser(this, problem);
                break;
        }
    }
}
