package se.gu.svanefalk.testgeneration.keystone;

import java.util.Map;

import de.uka.ilkd.key.logic.Term;

public enum KeYStone {
    INSTANCE;

    Preprocessor preprocessor = Preprocessor.getInstance();

    public Map<String, Number> solveConstraint(final Term constraint) {

        preprocessor.createMinimalProblemSet(constraint);

        return null;
    }
}