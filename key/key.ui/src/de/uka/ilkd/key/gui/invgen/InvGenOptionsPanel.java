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

import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.specgen.verificationrelationsystem.graph.VerificationRelationGraph;
import de.uka.ilkd.key.specgen.verificationrelationsystem.graph.VerificationRelationGraphGenerator;
import de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation.VerificationRelation;
import de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation.VerificationRelationGenerator;
import de.uka.ilkd.key.speclang.LoopSpecification;

/**
 * @author Jakob Laenge
 * 
 *         This class creates a Dialog to generate a loop Invariant (and Variant
 *         and Modifies).
 */
public class InvGenOptionsPanel {

	private static InvGenOptionsPanel generator = null;

	/**
	 * Singleton
	 */
	private InvGenOptionsPanel() {}

	/**
	 * Returns the single Instance of this class
	 */
	public static InvGenOptionsPanel getInstance() {
		if (generator == null) {
			generator = new InvGenOptionsPanel();
		}
		return generator;
	}

	/**
	 * Creates a Dialog. User can enter Invariant, Variant and Modifies clause. The
	 * Input is parsed and a new LoopInvariant is returned. In Case of a parser
	 * Exception an error-message is shown.
	 * 
	 * @param loopSpec
	 * @param services
	 * @param requiresVariant
	 * @param heapContext
	 * @return LoopSpec
	 */
	public LoopSpecification generateLoopSpecification(final LoopSpecification loopSpec, final Services services,
			final boolean requiresVariant, final List<LocationVariable> heapContext, IBuiltInRuleApp app, Goal goal) 
				throws RuleAbortException {
		/*VerificationRelationGenerator verificationRelationGenerator = VerificationRelationGenerator.getInstance();
		Set<VerificationRelation> verificationRelations = verificationRelationGenerator.generate(goal.sequent(), services);
		VerificationRelationGraphGenerator verificationRelationGraphGenerator = VerificationRelationGraphGenerator.getInstance();
		VerificationRelationGraph verificationRelationGraph = verificationRelationGraphGenerator.generate(verificationRelations);*/
		
        InvGenDialog dialog = new InvGenDialog(/*verificationRelationGraph*/null);
        dialog.dispose();
        if(dialog.getUserPressedCancel()) {
            throw new RuleAbortException("Automatic specification generation canceled by user.");
        }
        return dialog.getLoopSpecification();
	}
	
}
