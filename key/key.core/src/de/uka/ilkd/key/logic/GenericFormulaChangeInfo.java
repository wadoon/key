package de.uka.ilkd.key.logic;

import org.key_project.common.core.logic.GenericTerm;
import org.key_project.common.core.logic.Visitor;
import org.key_project.common.core.logic.calculus.GenericSequentFormula;
import org.key_project.common.core.program.GenericNameAbstractionTable;

public class GenericFormulaChangeInfo<S, N extends GenericNameAbstractionTable<S>, V extends Visitor<S,N,V,T>, 
    T extends GenericTerm<S,N,V,T>,SeqFor extends GenericSequentFormula<S, N, V, T>> {

    /** position within the original formula */
    protected final PosInOccurrence positionOfModification;
    /** modified formula */
    protected final SeqFor newFormula;

    public GenericFormulaChangeInfo(PosInOccurrence positionOfModification,
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
    public PosInOccurrence getPositionOfModification() {
        return positionOfModification;
    }

    public String toString() {
        return
                "Replaced " + positionOfModification +
                " with " + newFormula;
    }

}