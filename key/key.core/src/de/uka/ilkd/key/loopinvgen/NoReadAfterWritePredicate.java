package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;

public class NoReadAfterWritePredicate extends AbstractSortedOperator {
	public final static NoReadAfterWritePredicate SINGLETON = new NoReadAfterWritePredicate();

	public NoReadAfterWritePredicate() {
		super(new Name("no-read-after-write"), new Sort[] { Sort.ANY }, Sort.FORMULA, false);
	}

}
