package de.uka.ilkd.key.testgen.oracle;

public class OracleType implements OracleTerm {
	
	private org.key_project.common.core.logic.Sort s;

	public OracleType(org.key_project.common.core.logic.Sort s) {
		super();
		this.s = s;
	}
	
	public String toString(){
		
		return s.name().toString();
		
	}

}
