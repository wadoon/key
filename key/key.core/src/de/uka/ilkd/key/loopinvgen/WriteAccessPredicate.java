package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

public class WriteAccessPredicate extends AccessPredicate {

	public WriteAccessPredicate(Sort[] argSort, Sort ts) {
		super(new Name("write-access"), argSort, ts);
		// TODO Auto-generated constructor stub
	}

}
