package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

public final class ReadAccessPredicate extends AccessPredicate {

	public ReadAccessPredicate(Sort[] argSort, Sort ts) {
		super(new Name("read-access"), argSort, ts);
	}

}
