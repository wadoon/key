package de.uka.ilkd.key.smt.communication;

import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTSolverResult;

import javax.annotation.Nonnull;
import java.io.IOException;

/**
 * The socket for veriT.
 *
 * @author Alicia Appelhagen
 */
public class VeriTSocket extends AbstractSolverSocket {

    private static final String NO_PROOF_SET = "(error \"option :produce-proofs has not been set.\")";
    private static final String END_MODEL = "\"END_MODEL\"";
    private static final String BEGIN_PROOF = "\"BEGIN_PROOF\"";
    private static final String BEGIN_MODEL = "\"BEGIN_MODEL\"";

    private static String afterCheckSat = System.lineSeparator() + "(echo " + BEGIN_MODEL + ")"
            + System.lineSeparator() + "(get-model)"
            + System.lineSeparator() + "(echo " + END_MODEL + ")"
            + System.lineSeparator() + "(echo " + BEGIN_PROOF + ")"
            + System.lineSeparator() + "(get-proof)"
            + System.lineSeparator() + "(exit)"
            + System.lineSeparator();

    public VeriTSocket(String name, ModelExtractor query) {super(name, query);}

    @Override
    public void messageIncoming(@Nonnull Pipe pipe, @Nonnull String msg) throws IOException {
        SolverCommunication sc = pipe.getSolverCommunication();
        // Ignore whitespaces:
        msg = msg.trim();

        // If there hasn't already been a satisfiability answer, errors are a problem:
        if (msg.startsWith("error") || msg.startsWith("Invalid")) {
            sc.addMessage(msg, SolverCommunication.MessageType.ERROR);
            if (msg.contains("WARNING:")) {
                return;
            }
            throw new IOException("Error while executing " + getName() + ": " + msg);
        }

        // used only to steer the interaction with the solver and thus filtered out currently
        if (msg.equals("success")) {
            return;
        }

        if (msg.equals(BEGIN_MODEL) && sc.getState() != WAIT_FOR_MODEL) {
            // Do not print (start of) model if not waiting for a model
            return;
        }

        if (msg.equals(END_MODEL)) {
            if (sc.getState() == WAIT_FOR_DETAILS) {
                sc.setState(WAIT_FOR_PROOF);
                return;
            } else if (sc.getState() == WAIT_FOR_MODEL) {
                sc.setState(FINISH);
                return;
            }
        }

        switch (sc.getState()) {
            case WAIT_FOR_RESULT:
                if (msg.equals("unsat")) {
                    sc.setFinalResult(SMTSolverResult.createValidResult(getName()));
                    // get-proof was already sent, no need to send it again
                    // use get-proof's answer:
                    sc.setState(WAIT_FOR_DETAILS);
                }
                if (msg.equals("sat")) {
                    sc.setFinalResult(SMTSolverResult.createInvalidResult(getName()));
                    // get-model was already sent, no need to send it again
                    // use get-model's answer
                    sc.setState(WAIT_FOR_MODEL);
                }
                if (msg.equals("unknown")) {
                    sc.setFinalResult(SMTSolverResult.createUnknownResult(getName()));
                    // Ignore all answers to prematurely sent commands (get-proof/get-model)
                    // after check-sat:
                    sc.setState(FINISH);
                } else {
                    sc.addMessage(msg, SolverCommunication.MessageType.OUTPUT);
                }
                break;

            case WAIT_FOR_PROOF:
                sc.addMessage(msg, SolverCommunication.MessageType.OUTPUT);
                break;

            case WAIT_FOR_MODEL:
                sc.addMessage(msg, SolverCommunication.MessageType.OUTPUT);
                break;

            case FINISH:
                pipe.close();
                break;
        }
    }

    @Override
    public AbstractSolverSocket copy() {
        return new VeriTSocket(getName(), getQuery());
    }

    /**
     * The normal veriT builds don't support an interactive mode via stdin,
     * hence get-model/get-proof should be added to the input from the beginning:
     * Unlike the other solvers, the whole process needs to end before an answer to check-sat
     * is printed. Waiting for that answer and then sending get-proof/get-model accordingly
     * would mean sending the complete problem again.
     *
     * Luckily, that can be avoided by sending the two commands prematurely.
     * If the answer is sat, get-proof is ignored. If the answer is unsat, get-model is ignored.
     *
     * This only works because veriT always gives an answer to get-model and
     * get-model is sent anyway. It does end with an exception for a wrongly sent get-proof
     * though, hence get-model must be sent before get-proof.
     *
     * @param problem the SMT problem String to be modified
     * @return the given SMT problem ending with get-model and get-proof
     */
    @Override
    public String modifyProblem(String problem) {
        if (!problem.trim().endsWith(afterCheckSat)) {
            problem += afterCheckSat;
        }
        return problem;
    }
}