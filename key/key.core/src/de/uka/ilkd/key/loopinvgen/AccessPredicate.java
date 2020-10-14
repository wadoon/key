package de.uka.ilkd.key.loopinvgen;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;

public class AccessPredicate extends AbstractSortedOperator {

	public AccessPredicate(Name name, Sort[] argSort, Sort ts) {
		super(name,  new Sort[]{Sort.ANY, Sort.ANY}, Sort.FORMULA, true);
		// TODO Auto-generated constructor stub
	}
}
