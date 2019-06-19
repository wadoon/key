package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.util.HashSet;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.dependency_calculator.DependencyCalculator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.speclang.ClassInvariant;

public class CalculateDependenciesAction extends MainWindowAction {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public CalculateDependenciesAction(MainWindow mainWindow) {
		super(mainWindow);
		setName("dep");
		setTooltip("Calculates the dependencies for the given invariants");
		
		init();
	}
	
	public void init() {

		final KeYSelectionListener selListener = new KeYSelectionListener() {
			@Override
			public void selectedNodeChanged(KeYSelectionEvent e) {
				final Proof proof = getMediator().getSelectedProof();
				if (proof == null) {
					// no proof loaded
					setEnabled(false);
				} else {
					setEnabled(true);
				}
			}

			@Override
			public void selectedProofChanged(KeYSelectionEvent e) {
				selectedNodeChanged(e);
			}
		};
		getMediator().addKeYSelectionListener(selListener);

		// This method delegates the request only to the UserInterfaceControl which implements the functionality.
	    // No functionality is allowed in this method body!
	    getMediator().getUI().getProofControl().addAutoModeListener(new AutoModeListener() {
	      			@Override
	      			public void autoModeStarted(ProofEvent e) {
	      				getMediator().removeKeYSelectionListener(selListener);
	      				setEnabled(false);
	      			}
	      
	      			@Override
	      			public void autoModeStopped(ProofEvent e) {
	      				getMediator().addKeYSelectionListener(selListener);
	      				// selListener.selectedNodeChanged(null);
	      			}
	      		});
	    selListener.selectedNodeChanged(new KeYSelectionEvent(getMediator()
			        .getSelectionModel()));
		
	}

	@Override
	public void actionPerformed(ActionEvent arg0) {
		
		final Proof proof = getMediator().getSelectedProof();
		ContractPO contractPO = proof.getServices().getSpecificationRepository().getContractPOForProof(proof);
		KeYJavaType kjt  = contractPO.getContract().getKJT();
		
		HashSet<Term> dependencies = DependencyCalculator.calculateDependenciesForInvariants(proof,kjt);
		
		// Print out all the retrieved dependency terms
		for (Term term : dependencies) {
			System.out.println(term.toString());
		}
	}

}
