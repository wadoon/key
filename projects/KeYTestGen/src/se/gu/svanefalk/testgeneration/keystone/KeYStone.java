package se.gu.svanefalk.testgeneration.keystone;

import java.util.Calendar;
import java.util.Map;
import java.util.Set;

import se.gu.svanefalk.testgeneration.frontend.cli.CLIResources;
import se.gu.svanefalk.testgeneration.keystone.equations.EquationSystem;

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

        long time = Calendar.getInstance().getTimeInMillis();

        Set<Term> minimalProblemSet = preprocessor.createMinimalProblemSet(constraint);

        EquationSystem equationSystem = EquationSystem.createEquationSystem(minimalProblemSet);

        
        
        System.out.println("Run KeYStone: "
                + (Calendar.getInstance().getTimeInMillis() - time));

        return null;
    }
}