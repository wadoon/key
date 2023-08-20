package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.prover.TaskStartedInfo;

/**
 * Default implementation of a {@link TaskStartedInfo}.
 */
public record DefaultTaskStartedInfo(TaskKind kind, String message, int size) implements TaskStartedInfo {
    /**
     * {@inheritDoc}
     */
    @Override
    public TaskKind kind() {
        return kind;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String message() {
        return message;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int size() {
        return size;
    }
}
