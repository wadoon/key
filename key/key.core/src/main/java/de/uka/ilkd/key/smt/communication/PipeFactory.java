package de.uka.ilkd.key.smt.communication;

import de.uka.ilkd.key.smt.solvertypes.SolverType;

import java.io.InputStream;
import java.io.OutputStream;

public enum PipeFactory {

    BUFFERED_PIPE {
        @Override
        public BufferedPipe createPipe(String[] command, SolverCommunication session, SolverType type, Process process,
                                       InputStream input, OutputStream output) {
            return new BufferedPipe(command, session, type.getDelimiters(), type.getSendTriggers(), type.lineFeedback(),
                    process, input, output);
        }
    },

    SIMPLE_PIPE {
        @Override
        public SimplePipe createPipe(String[] command, SolverCommunication session, SolverType type, Process process,
                                       InputStream input, OutputStream output) {
            return new SimplePipe(input, type.getDelimiters(), output, session, process);
        }
    };

    public abstract Pipe createPipe(String[] command, SolverCommunication session, SolverType type, Process process,
                                    InputStream input, OutputStream output);

}


