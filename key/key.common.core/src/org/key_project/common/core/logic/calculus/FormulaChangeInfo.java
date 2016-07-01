package org.key_project.common.core.logic.calculus;


import org.key_project.common.core.logic.CCTerm;

/**
 * This class is used to hold information about modified formulas.
 * 
 * @see CCSemisequentChangeInfo
 * @see CCSequentChangeInfo
 */
public class FormulaChangeInfo<T extends CCTerm<?, ?, ?, T>> {

    /** position within the original formula */
    protected final PosInOccurrence<T> positionOfModification;
    
    /** modified formula */
    protected final SequentFormula<T> newFormula;

    public FormulaChangeInfo(PosInOccurrence<T> positionOfModification,
                             SequentFormula<T> newFormula) {
        this.newFormula = newFormula;
        this.positionOfModification = positionOfModification;
    }

    public SequentFormula<T> getNewFormula() {
        return newFormula;
    }

    public SequentFormula<T> getOriginalFormula() {
        return getPositionOfModification().sequentFormula();
    }

    /**
     * @return position within the original formula
     */
    public PosInOccurrence<T> getPositionOfModification() {
        return positionOfModification;
    }

    public String toString() {
        return "Replaced " + positionOfModification +
                " with " + newFormula;
    }

}