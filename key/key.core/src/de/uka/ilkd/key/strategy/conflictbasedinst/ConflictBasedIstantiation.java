package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Iterator;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;

/**
 * A conflict based instantiation generator for quantified terms.\
 *
 * @author Andre Challier <andre.challier@stud.tu-darmstadt.de>
 *
 */
public class ConflictBasedIstantiation implements TermGenerator {

	/*
	 * Singleton behavior
	 */

	// This objects singleton instance
	private static ConflictBasedIstantiation instance;

	// Prevent creation by other methods
	private ConflictBasedIstantiation() {
	}

	/**
	 * Returns the instance of this {@link ConflictBasedIstantiation} in a
	 * singleton-way.
	 * <p>
	 * Returns an instance of {@link ConflictBasedIstantiation} if one has been
	 * created. Otherwise a new instance will be created and returned.
	 *
	 * @return The instance of this {@link ConflictBasedIstantiation}
	 */
	public static ConflictBasedIstantiation getInstance() {
		if (ConflictBasedIstantiation.instance == null) {
			ConflictBasedIstantiation.instance = new ConflictBasedIstantiation();
		}
		return ConflictBasedIstantiation.instance;
	}

	/*
	 * TermGenerator behavior
	 */

	@Override
	public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
		// TODO Auto-generated method stub
		return null;
	}

}