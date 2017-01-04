package de.tud.cs.se.ds.psec.compiler;

import java.util.HashMap;

import org.objectweb.asm.Label;

/**
 * Helper class for maintaining global bytecode {@link Label}s.
 *
 * @author Dominic Scheurer
 */
public class GlobalLabelHelper {
    private HashMap<String, Label> globalLabels = new HashMap<>();

    /**
     * Stores a new global {@link Label} for the name of <code>label</code>.
     * 
     * @param label
     *            The name for the {@link Label} to store.
     * @throws RuntimeException
     *             If there is already a {@link Label} registered for this name.
     */
    public void registerGlobalLabel(String label) {
        if (!globalLabels.containsKey(label)) {
            globalLabels.put(label, new Label());
        } else {
            throw new RuntimeException(
                    "The global label " + label + " is already registered.");
        }
    }

    /**
     * Returns the global {@link Label} for name <code>label</code>.
     * 
     * @param label
     *            The name for the {@link Label} to return.
     * @return The global {@link Label} for name <code>label</code>.
     * @throws RuntimeException
     *             If there is no registered {@link Label} for this name.
     */
    public Label getGlobalLabel(String label) {
        if (globalLabels.containsKey(label)) {
            return globalLabels.get(label);
        } else {
            throw new RuntimeException(
                    "The global label " + label + " does not exist.");
        }
    }

    /**
     * Returns true iff there is a registered label for the given designator.
     * 
     * @param label
     *            The label name to check.
     * @return true iff there is a registered label for the given designator.
     */
    public boolean hasGlobalLabel(String label) {
        return globalLabels.containsKey(label);
    }

}
