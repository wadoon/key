package de.uka.ilkd.key.smt.communication;

import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.solvertypes.SolverType;

import javax.annotation.Nonnull;
import java.io.IOException;

public class VampireSocket extends AbstractSolverSocket {

    /**
     * Creates a new VampireSocket. Should not be called directly, better use the static factory method
     * {@link AbstractSolverSocket#createSocket(SolverType, ModelExtractor)}.
     *
     * @param name  the name of the solver
     * @param query the ModelExtractor for CE generation (unused by this socket)
     */
    public VampireSocket(String name, ModelExtractor query) {
        super(name, query);
    }

    @Override
    protected void handleMessage(@Nonnull Pipe pipe, @Nonnull String msg) throws IOException {
        SolverCommunication sc = pipe.getSolverCommunication();
        if (msg.contains("error") || msg.contains("exception")) {
            sc.addMessage(msg, SolverCommunication.MessageType.ERROR);
            if (msg.contains("WARNING:")) {
                return;
            }
            throw new IOException("Error while executing " + getName() + ": " + msg);
        }

        sc.addMessage(msg, SolverCommunication.MessageType.OUTPUT);

        switch (sc.getState()) {
            case WAIT_FOR_RESULT:
                if (msg.equals("unsat")) {
                    sc.setFinalResult(SMTSolverResult.createValidResult(getName()));
                    sc.setState(WAIT_FOR_DETAILS);
                }
                if (msg.equals("sat")) {
                    sc.setFinalResult(SMTSolverResult.createInvalidResult(getName()));
                    sc.setState(WAIT_FOR_DETAILS);

                }
                if (msg.equals("unknown")) {
                    sc.setFinalResult(SMTSolverResult.createUnknownResult(getName()));
                    sc.setState(WAIT_FOR_DETAILS);
                }
                break;

            case WAIT_FOR_DETAILS:
                break;
        }
    }

    /*
    Close the pipe immediately after sending the problem.
     */
    @Override
    public void communicate(Pipe pipe, String problem)
            throws IOException, InterruptedException {
        pipe.sendMessage(problem);
        // Close the solver's stdin immediately after sending the problem.
        // Note that no further messages can be sent after that.
        // (assumes an implementation of #sendEOF() like in {@link SimplePipe})
        pipe.sendEOF();
        String solverAnswer = pipe.readMessage();
        while (solverAnswer != null) {
            handleMessage(pipe, solverAnswer);
            solverAnswer = pipe.readMessage();
        }
        // Close the pipe (destroys the process).
        pipe.close();
    }

    @Override
    public AbstractSolverSocket copy() {
        return new VampireSocket(getName(), getQuery());
    }

}
