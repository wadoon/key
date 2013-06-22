package se.gu.svanefalk.testgeneration.keystone;

import java.util.Map;
import java.util.Set;

import se.gu.svanefalk.testgeneration.keystone.equations.EquationSystem;
import de.uka.ilkd.key.logic.Term;

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
}