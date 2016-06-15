package de.uka.ilkd.key.logic;

import org.key_project.common.core.logic.calculus.SequentFormula;

/**
 * This class is used to hold information about modified formulas.
 * 
 * @see GenericSemisequentChangeInfo
 * @see GenericSequentChangeInfo
 */
public class FormulaChangeInfo<SeqFor extends SequentFormula<?>> {

    /** position within the original formula */
    protected final PosInOccurrence<?, SeqFor> positionOfModification;
    /** modified formula */
    protected final SeqFor newFormula;

    public FormulaChangeInfo(PosInOccurrence<?, SeqFor> positionOfModification,
            SeqFor newFormula) {
        this.newFormula = newFormula;
        this.positionOfModification = positionOfModification;
    }

    public SeqFor getNewFormula() {
        return newFormula;
    }

    public SeqFor getOriginalFormula() {
        return getPositionOfModification().sequentFormula();
    }

    // FIXME (DS): We might have to include the Term type as generic argument
    // for callers of the method below...

    /**
     * @return position within the original formula
     */
    public PosInOccurrence<?, SeqFor> getPositionOfModification() {
        return positionOfModification;
    }

    public String toString() {
        return "Replaced " + positionOfModification +
                " with " + newFormula;
    }

}