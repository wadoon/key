package de.uka.ilkd.key.logic.op;

import java.util.WeakHashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class defines an update that represents a sequence (possibly empty) of events.
 * It takes as argument the timestamp t of the event issued directly before. This means 
 * if the update stands for sequence of length >= 1, the first event in this sequence would have
 * the timestamp t+1.
 * 
 * @author Asma
 *
 */
public class AnonEventUpdate extends AbstractSortedOperator {

	private static WeakHashMap<Sort, AnonEventUpdate> anonEventUpdates =
			new WeakHashMap<>();
	
	public static AnonEventUpdate getAnonEventUpdateFor(Services s) {
		Sort intSort = s.getTypeConverter().getIntegerLDT().targetSort();
		AnonEventUpdate evUpdate = null;
		synchronized(AnonEventUpdate.class) {
		    evUpdate = anonEventUpdates.get(intSort);
			if (evUpdate == null) {
				evUpdate = new AnonEventUpdate(intSort);
				anonEventUpdates.put(intSort, evUpdate);
			}
		}
		return evUpdate;
	}
	
	private AnonEventUpdate(Sort argSort) {
		super(new Name("\\eventStar"), new Sort[]{argSort}, Sort.UPDATE, false);
	}
	
	public String toString() {
		return "\\eventStar";
	}

}
