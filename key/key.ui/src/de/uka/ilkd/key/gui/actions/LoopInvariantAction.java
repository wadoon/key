package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.loopinvgen.LoopInvGenerator;
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
			LoopInvGenerator lig = new LoopInvGenerator(g);
			lig.setInvInSpec(null);
			System.out.println("fine");
		}
		
	}

}
