package org.keyproject.key.api.data;

public record TaskFinishedInfo() implements KeYDataTransferObject {
    public static TaskFinishedInfo from(de.uka.ilkd.key.prover.TaskFinishedInfo info) {
        return new TaskFinishedInfo();
    }
}
