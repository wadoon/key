package de.uka.ilkd.key.testgen.oracle;

import org.key_project.common.core.logic.SpecialSorts;

public class OracleConstant implements OracleTerm {
	
	private String value;
	
	private org.key_project.common.core.logic.Sort sort;
	
	public static final OracleConstant TRUE = new OracleConstant("true", SpecialSorts.FORMULA);
	public static final OracleConstant FALSE = new OracleConstant("false", SpecialSorts.FORMULA);
	
	public OracleConstant(String value, org.key_project.common.core.logic.Sort sort) {
		this.value = value;
		this.sort = sort;
	}

	public String getValue() {
		return value;
	}
	
	public org.key_project.common.core.logic.Sort getSort() {
	    return sort;
    }

	public void setSort(org.key_project.common.core.logic.Sort sort) {
	    this.sort = sort;
    }

	public String toString(){
		return value;
	}
	
	
}
