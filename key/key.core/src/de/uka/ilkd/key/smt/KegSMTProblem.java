package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;

public class KegSMTProblem extends SMTProblem{
	private final Services services;
	private final KeYJavaType typeOfClassUnderTest;
	public KegSMTProblem(Term term, Services services, KeYJavaType typeOfClassUnderTest){
		super(term);
		this.services = services;
		this.typeOfClassUnderTest = typeOfClassUnderTest;
	}
	public Services getServices() {
		return services;
	}
	public KeYJavaType getTypeOfClassUnderTest() {
		return typeOfClassUnderTest;
	}
	
	
}
