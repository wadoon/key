package se.gu.svanefalk.testgeneration.keystone;

import java.util.Map;

import se.gu.svanefalk.testgeneration.frontend.cli.CLIResources;

import de.uka.ilkd.key.logic.Term;

public class KeYStone {

    private static KeYStone instance = null;

    public static KeYStone getInstance() {
        if (instance == null) {
            instance = new KeYStone();
        }
        return instance;
    }

    private KeYStone() {

    }

    Preprocessor preprocessor = Preprocessor.getInstance();

    public Map<String, Number> solveConstraint(final Term constraint)
            throws KeYStoneException {

        preprocessor.createMinimalProblemSet(constraint);

        return null;
    }
}