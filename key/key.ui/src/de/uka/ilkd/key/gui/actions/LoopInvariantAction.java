package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Statement;
//import de.uka.ilkd.key.loopinvgen.DependenceLoopInvGenerator;
import de.uka.ilkd.key.proof.Goal;

public class LoopInvariantAction extends MainWindowAction {

	public LoopInvariantAction(MainWindow mainWindow) {
		super(mainWindow);
		setName("Loop Invariant");
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		final KeYMediator mediator = getMediator();
		
		Goal g = mediator.getSelectedGoal();
		if (g != null) {
			// loop invariant generation
		//	DependenceLoopInvGenerator lig = new DependenceLoopInvGenerator(g);
		
		//	lig.genLI();
		}
		
	}

}
