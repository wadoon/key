package de.uka.ilkd.key.smt;

import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.concurrent.locks.ReentrantLock;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.smt.SMTSolver.ReasonOfInterruption;
import de.uka.ilkd.key.smt.SMTSolver.SolverState;
import de.uka.ilkd.key.taclettranslation.assumptions.TacletSetTranslation;

/**
 * Represents the basis for an {@link SMTSolver} implementation, providing common data and utility
 * methods.
 */
public abstract class AbstractSMTSolver
        implements SMTSolver, Runnable {

    /**
     * Counter for creating unique identifiers for each individual solver instance.
     */
    protected static int IDCounter = 0;
    protected final int ID = IDCounter++;

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

    /**
     * Exceptions encounterd during the Taclet translation procedure.
     */
    protected Collection<Throwable> exceptionsForTacletTranslation =
            new LinkedList<Throwable>();

    public AbstractSMTSolver(SolverType type) {

        this.type = type;
    }

    /**
     * Formats a String, causing "(...)" parts to be split into separate, indented lines.
     * 
     * @param string
     *            the String to format
     * @return the resulting String of the formatting
     */
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

    /**
     * Translates the {@link Term} to be processed by the solver into a format readable by the
     * solver itself. For example, for many solvers this would be SMT-LIB or SMT-LIB2.
     * 
     * @param term
     *            the {@link Term} to translate.
     * @return the translated formula
     * @throws IllegalFormulaException
     *             in the event that the formula could not be translated, or else was unacceptable
     *             to the translator.
     * @throws IOException
     */
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

    /**
     * Starts a solver process. This method should be accessed only by an instance of
     * <code>SolverLauncher</code>. If you want to start a solver please have a look at
     * <code>SolverLauncher</code>.
     * 
     * @param timeout
     * @param settings
     */
    @Override
    public void startConcurrently(SolverTimeout timeout, SMTSettings settings) {

        thread = new Thread(this);
        solverTimeout = timeout;
        smtSettings = settings;
        thread.start();
    }

    /**
     * Starts the solver as part of the current thread.
     */
    @Override
    public void start(SolverTimeout timeout, SMTSettings settings) {

        solverTimeout = timeout;
        smtSettings = settings;
        run();
    }

    /**
     * @return an instance of {@link Throwable} in the event that an exception was raised during the
     *         solvers execution, <code>null</code> otherwise.
     */
    public Throwable getException() {

        return isRunning() ? null : exception;
    }

    /**
     * @return the {@link SMTProblem} associated with this particular solver session.
     */
    public SMTProblem getProblem() {

        return isRunning() ? null : problem;
    }

    /**
     * In the event that this solver session has been interrupted, return the corresponding
     * {@link ReasonOfInterruption} associated with the interruption.
     */
    @Override
    public ReasonOfInterruption getReasonOfInterruption() {

        return isRunning() ? ReasonOfInterruption.NoInterruption : reasonOfInterruption;
    }

    /**
     * @return the {@link SolverType} of this solver.
     */
    @Override
    public SolverType getType() {

        return type;
    }

    /**
     * @return the scheduled time of execution for this solversession.
     */
    @Override
    public long getStartTime() {

        if (solverTimeout == null) {
            return -1;
        }
        return solverTimeout.scheduledExecutionTime();
    }

    /**
     * @return the timeout value for this solver session.
     */
    @Override
    public long getTimeout() {

        if (solverTimeout == null) {
            return -1;
        }
        return solverTimeout.getTimeout();
    }

    /**
     * @return the current state of this solver session.
     */
    @Override
    public SolverState getState() {

        try {
            lockStateVariable.lock();
            SolverState b = solverState;
            return b;
        }
        finally {
            lockStateVariable.unlock();
        }
    }

    /**
     * Sets the current state of the solver session.
     * 
     * @param value
     *            new state of the solver
     */
    protected void setSolverState(SolverState value) {

        try {
            lockStateVariable.lock();
            solverState = value;
        }
        finally {
            lockStateVariable.unlock();
        }
    }

    /**
     * @return true if this solver session has been interrupted, false otherwise.
     */
    @Override
    public boolean wasInterrupted() {

        return getReasonOfInterruption() != ReasonOfInterruption.NoInterruption;
    }

    /**
     * @return true if this solver session is currently executing, false otherwise.
     */
    @Override
    public boolean isRunning() {

        return getState() == SolverState.Running;
    }

    /**
     * In the event that this solver session becomes interrupted, set the correct flag identifying
     * the source of the interruption.
     * 
     * @param reasonOfInterruption
     *            the reason for the interruption.
     */
    public void setReasonOfInterruption(ReasonOfInterruption reasonOfInterruption) {

        try {
            lockInterruptionVariable.lock();
            this.reasonOfInterruption = reasonOfInterruption;
        }
        finally {
            lockInterruptionVariable.unlock();
        }
    }

    /**
     * Set the reason why this solver session was interrupted, if any.
     * 
     * @param reasonOfInterruption
     *            the reason for interruption
     * @param exc
     *            the exception associated with the interruption (if any).
     */
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

    /**
     * Handling routine in the event that the solver session becomes interrupted. Depending on the
     * cause of the interruption, listeners to this session will be notified accordingly.
     * 
     * @param e
     */
    protected void interruptionOccurred(Throwable e) {

        ReasonOfInterruption reason = getReasonOfInterruption();
        switch (reason) {
            case Exception: // TODO: Is it really correct that these two are conflated?
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

    /**
     * @return the name of the type of this solver.
     */
    @Override
    public String name() {

        return type.getName();
    }

    /**
     * Interrupt the execution of this particular solver.
     * 
     * @param reason
     *            the reason for the interruption
     */
    @Override
    public void interrupt(ReasonOfInterruption reason) {

        // order of assignments is important;
        setReasonOfInterruption(reason);
        setSolverState(SolverState.Stopped);
        if (solverTimeout != null) {
            solverTimeout.cancel();
        }
    }

    /**
     * @return the {@link SMTSolverResult}, representing the result of the execution of the solver.
     */
    @Override
    public SMTSolverResult getFinalResult() {

        return isRunning() ? null : solverCommunication.getFinalResult();
    }

    /**
     * @return the translation of the Taclet set.
     */
    @Override
    public TacletSetTranslation getTacletTranslation() {

        return isRunning() ? null : tacletTranslation;
    }

    /**
     * @return the translation of the proof obligation(?).
     */
    @Override
    public String getTranslation() {

        return isRunning() ? null : problemString;
    }

    /**
     * @return a String with the ID of this particular solver instance.
     */
    @Override
    public String toString() {

        return name() + " (ID: " + ID + ")";
    }

    /**
     * Returns the output of the solver.
     */
    @Override
    public String getSolverOutput() {

        String output = "";
        output += "Result: " + solverCommunication.getFinalResult().toString() + "\n\n";

        for (String s : solverCommunication.getMessages()) {
            output += s + "\n";
        }
        return output;
    }

    /**
     * Return all {@link Throwable} instances raised in the course of execution of the solver.
     */
    @Override
    public Collection<Throwable> getExceptionsOfTacletTranslation() {

        return exceptionsForTacletTranslation;
    }
}
