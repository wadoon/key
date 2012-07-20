package de.uka.ilkd.keyabs.abs.abstraction;

import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.logic.Name;

public class ABSDatatype implements Type {

	private final Name dataType;
	
	@Override
	public String getFullName() {
		return dataType.toString();
	}

	public ABSDatatype(Name dataType) {
		super();
		this.dataType = dataType;
	}

	@Override
	public String getName() {
		return dataType.toString();
	}

	@Override
	public Literal getDefaultValue() {
		return null;
	}

	public String toString() {
		return getFullName();
	}
	
}
