package de.uka.ilkd.key.smt;

import java.io.PipedReader;
import java.io.PipedWriter;
import java.io.Reader;
import java.io.Writer;
import java.util.concurrent.locks.ReentrantLock;

import de.uni_freiburg.informatik.ultimate.smtinterpol.SMTInterface;

/**
 * Instances of this class represent autonomous invocations of the KeYnterpol
 * solver. It is functionally equivalent to {@link ExternalProcessLauncher},
 * with the exception that it runs an embedded version of the solver rather than
 * starting an external process.
 * 
 * @author christopher
 */
public class KeYnterpolLauncher<T> {

    /**
     * Lock for synchronizing access to this invocation of the SMT solver.
     */
    private ReentrantLock lockSession = new ReentrantLock(true);

    private final Pipe<T> pipe;

    Thread solverSessionThread;

    public KeYnterpolLauncher(T session, String[] messageDelimiters) {
        pipe = new Pipe<T>(session, messageDelimiters);
    }

    /**
     * Main procedure of the class. Starts the external process, then it goes
     * sleeping until the process has finished its work.
     */
    public void launch(final String[] command, String initialMessage,
            PipeListener<SolverCommunication> listener) throws Throwable {

        /*
         * Setup the pipe for communicating between the actual solver and the
         * classes using it. Two separate
         */
        PipedReader outputReader = new PipedReader();
        PipedWriter outputWriter = new PipedWriter(outputReader);

        PipedReader inputReader = new PipedReader();
        PipedWriter inputWriter = new PipedWriter(outputReader);

        PipedReader errorReader = new PipedReader();
        PipedWriter errorWriter = new PipedWriter(outputReader);

        // TODO: open a new session
        SMTSolverSession session = new SMTSolverSession(outputWriter,
                errorWriter, inputReader);
        
        solverSessionThread = new Thread(session);
        pipe.start(outputReader., output, error, listener)
        // send initial message: basically the smt problem.
        pipe.sendMessage(initialMessage + "\n");
        // pipe.closeSendingPipe();
        // wait until the output has been processed
        pipe.waitForPipe();

    }

    /**
     * Call this method only after the pipe has been stopped. It is not thread
     * safe!
     * 
     * @return
     */
    T getCommunication() {
        return pipe.getSession();
    }

    /**
     * Stops the external process: In particular the pipe is closed and the
     * process is destroyed.
     */
    public void stop() {
        lockSession.lock();
        try {
            pipe.close();
        } finally {
            lockSession.unlock();
        }
    }

    /**
     * Represents an autonomous run of the SMT solver (i.e. a mock "process").
     * 
     * @author christopher
     * 
     */
    private static class SMTSolverSession implements Runnable {

        /**
         * The outputstream for this solver session.
         */
        private Writer output;

        /**
         * The error stream for this session.
         */
        private Writer error;

        /**
         * The input stream for this session.
         */
        private Reader input;

        public SMTSolverSession(Writer output, Writer error, Reader input) {
            this.output = output;
            this.error = error;
            this.input = input;
        }

        @Override
        public void run() {

            SMTInterface smtInterface = SMTInterface.INSTANCE;
            smtInterface.startSession(output, error, input);
        }
    }
}
