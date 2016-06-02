package de.uka.ilkd.key.testgen.oracle;

public class OracleVariable implements OracleTerm {
	
	private String name;
	
	private org.key_project.common.core.logic.Sort sort;
	
	public OracleVariable(String name, org.key_project.common.core.logic.Sort sort) {
		this.name = name;
		this.sort = sort;
	}

	public String getName() {
		return name;
	}
	
	public org.key_project.common.core.logic.Sort getSort(){
		return sort;
	}
	
	public String toString(){
		return name;
	}
	
	
}
