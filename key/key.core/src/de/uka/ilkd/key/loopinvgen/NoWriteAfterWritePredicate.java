package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;

public class NoWriteAfterWritePredicate extends AbstractSortedOperator{

	public final static NoWriteAfterWritePredicate SINGLETON = new NoWriteAfterWritePredicate();

	public NoWriteAfterWritePredicate() {
		super(new Name("no-write-after-write"), new Sort[] { Sort.ANY }, Sort.FORMULA, false);
	}
}
