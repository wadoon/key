package de.uka.ilkd.key.logic;

/**
 * This class is used to hold information about modified formulas.
 *
 * @param positionOfModification position within the original formula
 * @param newFormula             modified formula
 * @see SequentChangeInfo
 */
public record FormulaChangeInfo(PosInOccurrence positionOfModification, SequentFormula newFormula) {

    public SequentFormula getOriginalFormula() {
        return positionOfModification().sequentFormula();
    }

    /**
     * @return position within the original formula
     */
    @Override
    public PosInOccurrence positionOfModification() {
        return positionOfModification;
    }

    public String toString() {
        return "Replaced " + positionOfModification + " with " + newFormula;
    }
}
