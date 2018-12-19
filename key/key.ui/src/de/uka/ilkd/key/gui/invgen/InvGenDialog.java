//This file is part of KeY - Integrated Deductive Software Design
//
//Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                      Technical University Darmstadt, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General
//Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.invgen;

import javax.swing.JDialog;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.specgen.verificationrelationsystem.graph.VerificationRelationGraph;
import de.uka.ilkd.key.speclang.LoopSpecification;

/**
 * @author Jakob Laenge
 * 
 * This class creates a Dialog to generate a loop Invariant and Variant and Modifies.
 */
public class InvGenDialog extends JDialog {

	private static final long serialVersionUID = 1273104615854912994L;

	
	
	/**
	 * Creates a Dialog. User can tune generation of Invariant, Variant and Modifies
	 * clause. The Input is parsed and a new LoopInvariant is returned. In Case of a
	 * parser Exception an error-message is shown.
	 * 
	 * @param loopInv
	 * @param services
	 * @return LoopInvariant
	 */
	public InvGenDialog(VerificationRelationGraph verificationRelationGraph) throws RuleAbortException {
		super(MainWindow.getInstance(), true);
		
		
		
	}

	public boolean getUserPressedCancel() {
		// TODO Auto-generated method stub
		return false;
	}

	public LoopSpecification getLoopSpecification() {
		// TODO Auto-generated method stub
		return null;
	}

}
