package de.uka.ilkd.key.ui;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.AbstractProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

public abstract class AbstractUserInterface<S extends IServices, IC extends InitConfig<S, IC>> implements UserInterface<S, IC> {

	public void loadProblem(File file, List<File> classPath,
	        File bootClassPath, KeYMediator<S, IC> mediator) {
		final ProblemLoader<S, IC> pl = createProblemLoader(file, classPath,
                bootClassPath, mediator);
		pl.addTaskListener(this);
		pl.run();
	}

    @Override
	public  IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
		if (app != null) {
			app = app.tryToInstantiate(goal);
		}
		// cannot complete that app
		return app.complete() ? app : null;
	}



    /**
     * {@inheritDoc}
     */
    @Override
    public DefaultProblemLoader load(File file, List<File> classPath, File bootClassPath) throws ProblemLoaderException {
       try {
          getMediator().stopInterface(true);
          DefaultProblemLoader loader = createDefaultProblemLoader(file, classPath, bootClassPath, getMediator());
          loader.load();
          return loader;
       }
       finally {
          getMediator().startInterface(true);
       }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Proof createProof(IC initConfig, ProofOblInput input) throws ProofInputException {
       AbstractProblemInitializer<?, IC> init = createProblemInitializer(true);
       return init.startProver(initConfig, input, 0);
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public void startAndWaitForAutoMode(Proof proof) {
       startAutoMode(proof);
       waitWhileAutoMode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void startAutoMode(Proof proof) {
       KeYMediator mediator = getMediator();
       mediator.setProof(proof);
       mediator.startAutoMode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void startAutoMode(Proof proof, ImmutableList<Goal> goals) {
       KeYMediator mediator = getMediator();
       mediator.setProof(proof);
       mediator.startAutoMode(goals);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void stopAutoMode() {
       getMediator().stopAutoMode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void waitWhileAutoMode() {
       while (getMediator().autoMode()) { // Wait until auto mode has stopped.
          try {
             Thread.sleep(100);
          }
          catch (InterruptedException e) {
          }
       }
    }
}
