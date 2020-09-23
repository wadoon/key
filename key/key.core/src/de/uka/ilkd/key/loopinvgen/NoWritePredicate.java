package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;

public class NoWritePredicate extends AbstractSortedOperator {

	public final static NoWritePredicate SINGLETON = new NoWritePredicate();

	public NoWritePredicate() {
		super(new Name("no-write"), new Sort[] { Sort.ANY }, Sort.FORMULA, false);
	}

}
