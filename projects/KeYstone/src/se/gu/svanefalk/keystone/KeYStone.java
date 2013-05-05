package se.gu.svanefalk.keystone;

import java.util.Map;
import java.util.Set;

import se.gu.svanefalk.testgeneration.keystone.Preprocessor;

import de.uka.ilkd.key.logic.Term;

public enum KeYStone {
    INSTANCE;

    Preprocessor preprocessor = Preprocessor.getInstance();

    public Map<String, Number> solveConstraint(Term constraint) {

        Set<Term> minimalProblemSet = preprocessor.createMinimalProblemSet(constraint);

        
        return null;
    }
}