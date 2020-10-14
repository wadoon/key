package de.uka.ilkd.key.loopinvgen;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

public class WriateAccessPredicate extends AccessPredicate {

	protected WriateAccessPredicate(Name name, ImmutableArray<Sort> argSorts, Sort sort, boolean isRigid, int timeStamp) {
		super(new Name("write-access-predicate"), argSorts, Sort.FORMULA, true);
		// TODO Auto-generated constructor stub
	}

}
