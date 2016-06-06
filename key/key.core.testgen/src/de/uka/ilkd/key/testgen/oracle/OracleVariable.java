package de.uka.ilkd.key.testgen.oracle;

import org.key_project.common.core.logic.sort.Sort;

public class OracleVariable implements OracleTerm {
	
	private String name;
	
	private Sort sort;
	
	public OracleVariable(String name, Sort sort) {
		this.name = name;
		this.sort = sort;
	}

	public String getName() {
		return name;
	}
	
	public Sort getSort(){
		return sort;
	}
	
	public String toString(){
		return name;
	}
	
	
}
