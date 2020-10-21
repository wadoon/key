package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.util.ArrayList;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.expression.operator.ComparativeOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.loopinvgen.ConstructAllCompPreds;
import de.uka.ilkd.key.loopinvgen.ConstructAllDepPreds;
import de.uka.ilkd.key.loopinvgen.ReadProof;
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
			ReadProof lig = new ReadProof(g);
			lig.getLoopFormula();
			lig.getArray();
//			lig.getLoopBody();

			Sort[] a = null;//How can I initialize it?
			//ConstructAllDepPreds cap = new ConstructAllDepPreds(g, a, 0, 4, 9);
//			ConstructAllCompPreds cacp = new ConstructAllCompPreds(0, 4, 9);
//			ArrayList<ComparativeOperator> co = cacp.consAllCompPreds();
//			if(co != null)
//				System.out.println(co);
		}
		
	}

}
