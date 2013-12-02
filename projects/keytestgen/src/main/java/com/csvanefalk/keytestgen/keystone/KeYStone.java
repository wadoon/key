package com.csvanefalk.keytestgen.keystone;

import com.csvanefalk.keytestgen.keystone.equations.EquationSystem;
import de.uka.ilkd.key.logic.Term;

import java.util.Map;
import java.util.Set;

public class KeYStone {

    private static KeYStone instance = null;

    public static KeYStone getInstance() {
        if (KeYStone.instance == null) {
            KeYStone.instance = new KeYStone();
        }
        return KeYStone.instance;
    }

    Preprocessor preprocessor = Preprocessor.getInstance();

    private KeYStone() {

    }

    public Map<String, Integer> solveConstraint(final Term constraint)
            throws KeYStoneException {

        final Set<Term> minimalProblemSet = preprocessor.createMinimalProblemSet(constraint);

        final EquationSystem equationSystem = EquationSystem.createEquationSystem(minimalProblemSet);

        final Map<String, Integer> result = equationSystem.experimentalSolve();

        return result;
    }

    public void __DEBUG_DISPOSE() {
        instance = null;
    }
}