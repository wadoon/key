package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;

public class NoWriteAfterReadPredicate extends AbstractSortedOperator{

	public final static NoWriteAfterReadPredicate SINGLETON = new NoWriteAfterReadPredicate();

	public NoWriteAfterReadPredicate() {
		super(new Name("no-write-after-read"), new Sort[] { Sort.ANY }, Sort.FORMULA, false);
	}

}
