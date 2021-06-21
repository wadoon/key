// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.smt.processcomm;

import de.uka.ilkd.key.smt.processcomm.SolverCommunication.Message;

import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;


/**
 * This class is responsible for starting external processes:
 * 1. It creates the process
 * 2. Creates a pipe, that is used for communication.
 * 3. Starts the process and waits until the pipe has been closed or the process has been stopped.
 * Remark: It blocks the invoking thread.
 */
public class ExternalProcessLauncher {

    private final SolverCommunication session;
    private final String[] delimiters;
    private final AbstractSolverSocket socket;

    private BufferedMessageReader bmr;

    private Process process;

    public ExternalProcessLauncher(AbstractSolverSocket socket, SolverCommunication session, String[] messageDelimiters) {
        this.session = session;
        this.delimiters = messageDelimiters;
        this.socket = socket;
    }

    /**
     * Main procedure of the class. Starts the external process, then it goes sleeping until 
     * the process has finished its work.
     */
    public void launch(final String[] command, String solverInput) throws IOException, InterruptedException {
        try {
            ProcessBuilder builder = new ProcessBuilder(command);

            // redirect stderr to stdout
            builder.redirectErrorStream(true);

            process = builder.start();

            bmr = new BufferedMessageReader(new InputStreamReader(process.getInputStream()),
                    delimiters);

            // limitation: solverInput has to be given completely at solver start
            process.getOutputStream().write(solverInput.getBytes(StandardCharsets.UTF_8));
            process.getOutputStream().flush();

            String message = bmr.readMessage();
            while (message != null) {
                socket.messageIncoming(session, new Message(message, SolverCommunication.MessageType.Output));
                message = bmr.readMessage();
            }
        } catch (Exception ex) {
            stop();
            throw ex;
        }
    }

    /**
     * Stops the external process: In particular the pipe is closed and the process is destroyed. 
     */
    public void stop() {
        if(process != null){
            process.destroy();
        }
    }
}
