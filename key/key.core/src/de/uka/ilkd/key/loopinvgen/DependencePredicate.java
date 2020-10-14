package de.uka.ilkd.key.loopinvgen;

import org.key_project.util.collection.ImmutableArray;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * There are five different dependence predicate.
 * 
 * @author Asma
 *
 */
public class DependencePredicate extends AbstractSortedOperator {

	public DependencePredicate(Name name, Sort[] argSorts) {
		super(name, new ImmutableArray<Sort>(argSorts), Sort.FORMULA, false);
		// TODO Auto-generated constructor stub
	}

}
