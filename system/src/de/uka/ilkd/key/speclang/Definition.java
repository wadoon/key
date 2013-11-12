package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.logic.Term;

public class Definition {
	private String name;
	private Term definition;
	public Definition(String name, Term definition) {
		super();
		this.name = name;
		this.definition = definition;
		System.out.println("Def" + name + " created!");
	}
	

	
}

