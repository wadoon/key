package de.uka.ilkd.key.smt.communication;

import javax.annotation.Nonnull;
import java.io.*;
import java.util.*;

public class BufferedPipe implements Pipe {

    private static String EXIT = "(exit)";

    private Process process;
    private boolean closed;
    private BufferedWriter writer;
    private BufferedReader reader;

    private final String[] command;
    private final List<String> sendTriggers;
    private final SolverCommunication session;
    private final List<String> sentMessages;
    private final List<String> readLines;
    private final Iterator<String> readIterator;
    private final boolean lineFeedback;

    public BufferedPipe(String[] command, SolverCommunication session, String[] messageDelimiters,
                        String[] sendTriggers, boolean lineFeedback, Process process, InputStream input,
                        OutputStream output) {
        this.session = session;
        this.sentMessages = new ArrayList<>();
        this.sendTriggers = Arrays.asList(sendTriggers);
        this.readLines = new LinkedList<>();
        this.readIterator = new Iterator<String>() {
            private int readIndex = 0;

            @Override
            public boolean hasNext() {
                return readIndex < readLines.size();
            }

            @Override
            public String next() {
                return readLines.get(readIndex++);
            }
        };
        this.lineFeedback = lineFeedback;
        this.command = command;
        this.process = process;
        writer = new BufferedWriter(new OutputStreamWriter(output));
        reader =  new BufferedReader(new InputStreamReader(input));
        closed = false;
    }

    private void buildProcess() throws IOException {
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.redirectErrorStream(true);
        process = builder.start();
    }

    private void write() throws IOException {
        for (String msg: sentMessages) {
            session.addMessage(msg, SolverCommunication.MessageType.INPUT);
            writer.write(msg + System.lineSeparator());
            writer.flush();
        }
        // Close the writer so that the process answers.
        writer.close();
    }

    private void read() throws IOException {
        // Read the answer and add it to the puffer of read messages.
        String msg = reader.readLine();
        int counter = 0;
        int readByNow = readLines.size();
        while (msg != null) {
            counter++;
            if (!lineFeedback || counter > readByNow) {
                readLines.add(msg + System.lineSeparator());
            }
            msg = reader.readLine();
        }
        reader.close();
    }


    @Override
    public void sendMessage(String message) throws IOException {
        if (closed) {
            throw new IOException("Pipe has been closed.");
        }
        // Add the message to the sent message buffer as it will have to be used again for further communication.
        sentMessages.add(message);
        boolean shouldSend = sendTriggers.stream().anyMatch(s -> message.trim().contains(s));
        if (!shouldSend && !sendTriggers.isEmpty()) {
            return;
        }
        write();
        read();
        // End the process and create it anew for further communication.
        process.destroy();
        buildProcess();
        writer = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
        reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
    }

    @Override
    public String readMessage() throws IOException, InterruptedException {
        if (closed) {
            throw new IOException("Pipe has been closed.");
        }
        if (!readIterator.hasNext()) {
            return null;
        }
        return readIterator.next();
    }

    @Nonnull
    @Override
    public SolverCommunication getSolverCommunication() {
        return session;
    }

    @Override
    public void close() {
        process.destroy();
        closed = true;
    }

    @Override
    public void sendEOF() {
        try {
            write();
            read();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

}
