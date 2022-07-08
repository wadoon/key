package de.uka.ilkd.key.smt.communication;

import de.uka.ilkd.key.smt.SMTSolverImplementation;
import org.key_project.util.java.IOUtil;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import java.io.*;
import java.util.Arrays;

/**
 * This class is responsible for starting external processes:
 * <ol>
 * <li> It creates the process (stderr is merged to stdout).</li>
 * <li> Creates the pipe that is used for communication.</li>
 * <li> Starts the process and returns. </li>
 * </ol>
 * Remark: Does not block the invoking thread.
 *
 * @author Wolfram Pfeifer (overhaul)
 */
public class ExternalProcessLauncher {
    private static final Logger LOGGER = LoggerFactory.getLogger(ExternalProcessLauncher.class);

    /**
     * the store of all messages send to and received from the external process
     */
    private final @Nonnull
    SolverCommunication session;

    /**
     * the delimiters which separate the messages
     */
    private final @Nonnull
    String[] messageDelimiters;

    /**
     * the external process
     */
    private Process process;

    /**
     * the pipe for sending and receiving to/from the process
     */
    private SimplePipe pipe;

    /**
     * Creates the external process launcher.
     *
     * @param session           the store for the messages send to and received from the process
     * @param messageDelimiters delimiters which separate the messages
     */
    public ExternalProcessLauncher(@Nonnull SolverCommunication session,
                                   @Nonnull String[] messageDelimiters) {
        this.session = session;
        this.messageDelimiters = messageDelimiters;
    }

    /**
     * Main procedure of the class. Starts the external process and connects the pipe to it.
     * stderr and stdout of the process are merged.
     *
     * @param command command (program and arguments) which is used to start the external process
     * @throws IOException if an I/O error occurs
     */
    public void launch(final String[] command) throws IOException {
        try {
            LOGGER.info("Run smt solver {}", Arrays.toString(command));
            ProcessBuilder builder = new ProcessBuilder(command);
            builder.redirectErrorStream(true);
            process = builder.start();
            InputStream input = process.getInputStream();
            OutputStream output = process.getOutputStream();
            pipe = new SimplePipe(input, messageDelimiters, output, session, process);
        } catch (IOException ex) {
            stop();
            throw ex;
        }
    }

    /**
     * Stops the external process: In particular the pipe is closed and the process is destroyed.
     */
    public void stop() {
        if (process != null) {
            var handle = process.toHandle();
            LOGGER.info("Stopping process {}, {}", handle.pid(), handle.info());
            pipe.close();
            handle.destroy();
            if (handle.isAlive()) {
                handle.destroyForcibly();
            }
        }
    }

    public Pipe getPipe() {
        return pipe;
    }
}
