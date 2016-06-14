package de.uka.ilkd.key.logic;

import org.key_project.common.core.logic.GenericTerm;
import org.key_project.common.core.logic.calculus.SequentFormula;

/**
 * This class is used to hold information about modified formulas.
 * @see GenericSemisequentChangeInfo
 * @see GenericSequentChangeInfo
 */
public class FormulaChangeInfo<T extends GenericTerm<?, ?, ?, T>, SeqFor extends SequentFormula<T>> {

    /** position within the original formula */
    protected final PosInOccurrence<T, SeqFor> positionOfModification;
    /** modified formula */
    protected final SeqFor newFormula;

    public FormulaChangeInfo(PosInOccurrence<T, SeqFor> positionOfModification,
            SeqFor newFormula) {
        this.newFormula = newFormula;
        this.positionOfModification = positionOfModification;
    }


    public SeqFor getNewFormula() {
        return newFormula;
    }

    public SeqFor getOriginalFormula() {
        return getPositionOfModification ().sequentFormula ();
    }

    /**
     * @return position within the original formula
     */
    public PosInOccurrence<T, SeqFor> getPositionOfModification() {
        return positionOfModification;
    }

    public String toString() {
        return
                "Replaced " + positionOfModification +
                " with " + newFormula;
    }

}