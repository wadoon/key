package de.uka.ilkd.key.testgen.oracle;

import org.key_project.common.core.logic.sort.Sort;

public class OracleType implements OracleTerm {
	
	private Sort s;

	public OracleType(Sort s) {
		super();
		this.s = s;
	}
	
	public String toString(){
		
		return s.name().toString();
		
	}

}
