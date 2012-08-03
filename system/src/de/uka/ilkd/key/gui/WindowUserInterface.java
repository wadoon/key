package de.uka.ilkd.key.gui;



import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;

/**
 * This class is the starting point for the extraction of a unified
 * Userinterface for a GUI refactoring.
 * 
 * It gathers all present interfaces and redirects action to the mainWindow.
 * 
 * It is subject to change a lot at the moment.
 * 
 * @author mattias ulbrich
 */

public class WindowUserInterface extends AbstractWindowUserInterface<Services, InitConfig> {

    public WindowUserInterface(MainWindow mainWindow) {
        super(mainWindow);
        completions.add(new FunctionalOperationContractCompletion());
        completions.add(new DependencyContractCompletion());
        completions.add(new LoopInvariantRuleCompletion());
    }

    @Override
    public ProblemInitializer createProblemInitializer(boolean registerProof) {
        return new ProblemInitializer(this, mainWindow.<Services, InitConfig>getMediator().getProfile(), registerProof,  this);
    }
}
