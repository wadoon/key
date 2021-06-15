package keyext.extract_preconditions.macros;

import de.uka.ilkd.key.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.proof.Goal;

/**
 * Based on de.uka.ilkd.key.macros.PreconditionSemanticsBlastingMacro
 */
public final class PreconditionSemanticsBlastingMacro extends SemanticsBlastingMacro {

	public PreconditionSemanticsBlastingMacro() {
		super();
		allowedPullOut.remove("store");
	}


	protected void addInvariantFormula(Goal goal) {
		// DO NOTHING
		return;
	}

}
