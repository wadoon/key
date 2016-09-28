package de.tud.cs.se.ds.psec.parser.ast;

/**
 * A container class for inputs that are relevant for assessing the
 * applicability of a translation rule.
 *
 * @author Dominic Scheurer
 */
public class ApplicabilityCheckInput {

    private int numChildren;

    /**
     * @param numChildren
     *            The number of children in the symbolic execution taclet AST.
     */
    public ApplicabilityCheckInput(int numChildren) {
        this.numChildren = numChildren;
    }

    /**
     * @return The number of children in the symbolic execution taclet AST.
     */
    public int getNumChildren() {
        return numChildren;
    }

}
