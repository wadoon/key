package se.gu.svanefalk.keystone;

import java.util.Map;

import se.gu.svanefalk.testgeneration.keystone.KeYStoneException;
import se.gu.svanefalk.testgeneration.keystone.Preprocessor;
import de.uka.ilkd.key.logic.Term;

public enum KeYStone {
    INSTANCE;

    Preprocessor preprocessor = Preprocessor.getInstance();

    public Map<String, Number> solveConstraint(final Term constraint)
            throws KeYStoneException {

        preprocessor.createMinimalProblemSet(constraint);

        return null;
    }
}