package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;

public final class NoReadPredicate extends AbstractSortedOperator {
	public final static NoReadPredicate SINGLETON = new NoReadPredicate();

	public NoReadPredicate() {
		super(new Name("no-read"), new Sort[] { Sort.ANY }, Sort.FORMULA, false);
	}

}
