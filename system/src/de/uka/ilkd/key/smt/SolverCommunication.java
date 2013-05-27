// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.smt;

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

/**
 * Stores the communication between KeY and an external solver: Contains a list
 * that stores the messages that has been sent from the solver to KeY and vice
 * versa.
 * 
 * Further, it also contains the final result of the solver.
 */
public class SolverCommunication {

    public SolverCommunication() {
    }

    /**
     * The default solver communicator.
     */
    public static SolverCommunication EMPTY = new SolverCommunication();

    /**
     * Messages passed between KeY and the SMT solver.
     */
    private final List<String> messages = Collections
            .synchronizedList(new LinkedList<String>());

    /**
     * The final result of the solving process.
     */
    private SMTSolverResult finalResult = SMTSolverResult.NO_IDEA;

    /**
     * The state of the solver.
     */
    private int state = 0;

    /**
     * Flag if the final result has already been set.
     */
    private boolean resultHasBeenSet = false;

    /**
     * Exceptions raised in the solving process.
     */
    private List<Throwable> exceptions = Collections
            .synchronizedList(new LinkedList<Throwable>());

    /**
     * Returns all messages that were sent between KeY and the solver.
     */
    public Iterable<String> getMessages() {
        // return an new iterable object in order to guarantee that the list of
        // messgages
        // cannot be changed.
        return new Iterable<String>() {

            @Override
            public Iterator<String> iterator() {
                return messages.iterator();
            }
        };
    }

    /**
     * Call this method only if you are sure that there are no other threads
     * accessing it. It is not thread safe, but it is designed for belated
     * analysis.
     * 
     * @return
     */
    public Iterable<Throwable> getExceptions() {
        return new Iterable<Throwable>() {

            @Override
            public Iterator<Throwable> iterator() {
                return exceptions.iterator();
            }
        };
    }

    /**
     * @return true if at least one excpetion has been raised in the course of
     *         execution.
     */
    public boolean exceptionHasOccurred() {
        return !exceptions.isEmpty();
    }

    /**
     * @return the final result of the solving process.
     */
    public SMTSolverResult getFinalResult() {
        return finalResult;
    }

    /**
     * Returns the current state of the communication. The states are defined by
     * the solver classes.
     */
    public int getState() {
        return state;
    }

    /**
     * @return true if the result of the associated solver session has been set.
     */
    public boolean resultHasBeenSet() {
        return resultHasBeenSet;
    }

    /**
     * Set the final result of the solving process.
     * 
     * @param finalResult
     */
    void setFinalResult(SMTSolverResult finalResult) {

        /*
         * append the output from the solver to the result before returning it.
         */
        finalResult.setOutput(messages);

        this.finalResult = finalResult;
        resultHasBeenSet = true;
    }

    /**
     * Adds a message to the communicator.
     * 
     * @param message
     *            the message
     */
    void addMessage(String message) {
        messages.add(message);
    }

    /**
     * Set the state of the communicator.
     * 
     * @param state
     *            new state
     */
    void setState(int state) {
        this.state = state;
    }

    /**
     * Adds an exception to the communicators buffer.
     * 
     * @param e
     *            the exception
     */
    void addException(Throwable e) {
        exceptions.add(e);
    }

    /**
     * Instances of this class represent messages passed between the solver and
     * KeY.
     */
    public static class Message {

        /**
         * The message type depends on the channel which was used for sending
         * the message.
         */
        public enum MessageType {
            Input, Output, Error
        };

        /**
         * The content of the message.
         */
        private final String content;

        /**
         * The type pf the message.
         */
        private final MessageType type;

        /**
         * Creates a new message of a certain type with specific content.
         * 
         * @param content
         * @param type
         */
        public Message(String content, MessageType type) {
            this.content = content;
            this.type = type;
        }

        /**
         * @return the content of the message.
         */
        public String getContent() {
            return content;
        }

        /**
         * @return the type of the message.
         */
        public MessageType getType() {
            return type;
        }
    }
}