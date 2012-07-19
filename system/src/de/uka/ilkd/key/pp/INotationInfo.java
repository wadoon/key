package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.op.Operator;

public interface INotationInfo {

	public abstract void refresh(IServices services);

	public abstract AbbrevMap getAbbrevMap();

	public abstract void setAbbrevMap(AbbrevMap am);

	/** Get the Notation for a given Operator.  
	 * If no notation is registered, a Function notation is returned.
	 */
	public abstract INotation getNotation(Operator op, IServices services);

}