package org.key_project.slicing;

/**
 * Graph node used if a rule application did not use any input formulas.
 */
public class PseudoInput implements GraphNode {
    @Override
    public String toString(boolean abbreviated) {
        return "pseudo input " + Integer.toHexString(hashCode());
    }
}
