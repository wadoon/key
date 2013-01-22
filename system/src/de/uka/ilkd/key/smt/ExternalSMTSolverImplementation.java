// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;

final class ExternalSMTSolverImplementation extends AbstractSMTSolver {

    /** starts a external process and returns the result */
    private ExternalProcessLauncher<SolverCommunication> processLauncher;

    ExternalSMTSolverImplementation(SMTProblem problem,
            SolverListener listener, Services services, SolverType myType) {
        super(myType);
        this.problem = problem;
        this.listener = listener;
        this.services = services;
        processLauncher = new ExternalProcessLauncher<SolverCommunication>(
                new SolverCommunication(), type.getDelimiters());

    }

    @Override
    public void run() {

        /*
         * Firstly: Set the state to running and inform the listener.
         */
        setSolverState(SolverState.Running);
        listener.processStarted(this, problem);

        /*
         * Secondly: Translate the given problem into a format acceptable by the
         * SMT solver.
         */
        String commands[];
        try {
            // TODO: This should be done in two separate methods.
            commands = translateToCommand(problem.getTerm());
        } catch (Throwable e) {
            interruptionOccurred(e);
            listener.processInterrupted(this, problem, e);
            setSolverState(SolverState.Stopped);
            solverTimeout.cancel();
            return;
        }

        /*
         * Start the external process.
         */
        try {
            processLauncher.launch(commands, type.modifyProblem(problemString),
                    type);

            solverCommunication = processLauncher.getCommunication();
            if (solverCommunication.exceptionHasOccurred()
                    && !solverCommunication.resultHasBeenSet()) {

                /*
                 * if the result has already been set, the exceptions must have
                 * occurred while doing the remaining communication, which is
                 * not that important.
                 */
                throw new AccumulatedException(
                        solverCommunication.getExceptions());
            }

            // uncomment for testing
            // Thread.sleep(3000);
            // uncomment for testing
            // Random random = new Random();
            // Thread.sleep(random.nextInt(3000)+1000);
            // throw new RuntimeException("Test exception");
        } catch (Throwable e) {
            interruptionOccurred(e);
        } finally {
            // Close every thing.
            solverTimeout.cancel();
            setSolverState(SolverState.Stopped);
            listener.processStopped(this, problem);
        }
    }

    /**
     * Interrupts the solver process.
     */
    @Override
    public void interrupt(ReasonOfInterruption reason) {

        super.interrupt(reason);

        if (thread != null) {
            processLauncher.stop();
            thread.interrupt();
        }
    }
}
