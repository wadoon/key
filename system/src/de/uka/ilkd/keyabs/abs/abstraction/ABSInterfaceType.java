package de.uka.ilkd.keyabs.abs.abstraction;

import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.logic.Name;

public class ABSInterfaceType implements Type {

	private final Name interfaceTypeName;
	
	
	public ABSInterfaceType(Name name) {
		this.interfaceTypeName = name;
	}

	@Override
	public String getFullName() {
		return interfaceTypeName.toString();
	}

	@Override
	public String getName() {
		return interfaceTypeName.toString();
	}

	@Override
	public Literal getDefaultValue() {
		return null;
	}

}
