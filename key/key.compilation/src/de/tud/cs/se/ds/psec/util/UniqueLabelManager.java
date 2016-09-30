package de.tud.cs.se.ds.psec.util;

import java.util.HashMap;

import org.objectweb.asm.Label;

/**
 * This class keeps track of names for {@link Label}s (that have to be unique
 * per translation definition) and makes sure that a givne label name is always
 * assigned the same {@link Label}.
 *
 * @author Dominic Scheurer
 */
public class UniqueLabelManager {

    private HashMap<String, Label> labelMap = new HashMap<>();

    /**
     * Returns the same label for a given labelName.
     * 
     * @param labelName
     *            The name of the {@link Label}.
     * @return A corresponding {@link Label} object.
     */
    public Label getLabelForName(String labelName) {
        Label result;

        if (labelMap.containsKey(labelName)) {
            result = labelMap.get(labelName);
        }
        else {
            result = new Label();
            labelMap.put(labelName, result);
        }

        return result;
    }
}
