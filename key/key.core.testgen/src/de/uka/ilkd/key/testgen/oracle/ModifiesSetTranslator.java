package de.uka.ilkd.key.testgen.oracle;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.JavaDLTerm;

public class ModifiesSetTranslator {
	
	private Services services;
	private OracleGenerator gen;
	
	
	public boolean isSingleTon(JavaDLTerm t){		
		return t.op().equals(getLocSetLDT().getSingleton());		
	}
	
	public boolean isUnion(JavaDLTerm t){
		return t.op().equals(getLocSetLDT().getUnion());
	}
	
	public boolean isIntersection(JavaDLTerm t){
		return t.op().equals(getLocSetLDT().getIntersect());
	}
	
	public boolean isAllFields(JavaDLTerm t){
		return t.op().equals(getLocSetLDT().getAllFields());
	}
	
	public boolean isAllLocs(JavaDLTerm t){
		return t.op().equals(getLocSetLDT().getAllLocs());
	}
	
	public boolean isEmpty(JavaDLTerm t){
		return t.op().equals(getLocSetLDT().getEmpty());
	}	
	
	private LocSetLDT getLocSetLDT(){
		return services.getTheories().getLocSetLDT();
	}	
	
	public ModifiesSetTranslator(Services services, OracleGenerator gen) {
		this.services = services;
		this.gen = gen;
	}
	
	
	public OracleLocationSet translate(JavaDLTerm t){
		
		if(isSingleTon(t)){
			JavaDLTerm obj = t.sub(0);
			JavaDLTerm field = t.sub(1);			
			String objString = gen.generateOracle(obj, false).toString();
			String fieldString = gen.generateOracle(field, false).toString();			
			OracleLocation loc = new OracleLocation(objString, fieldString);
			return OracleLocationSet.singleton(loc);			
		}
		
		else if(isUnion(t)){			
			OracleLocationSet left = translate(t.sub(0));
			OracleLocationSet right = translate(t.sub(1));			
			return OracleLocationSet.union(left, right);			
		}
		
		else if(isIntersection(t)){
			OracleLocationSet left = translate(t.sub(0));
			OracleLocationSet right = translate(t.sub(1));
			return OracleLocationSet.intersect(left, right);
		}
		
		else if(isAllFields(t)){
			JavaDLTerm obj = t.sub(0);
			String objString = gen.generateOracle(obj, false).toString();
			OracleLocation loc = new OracleLocation(objString);
			return OracleLocationSet.singleton(loc);
		}
		
		else if(isEmpty(t)){
			return OracleLocationSet.EMPTY;
		}
		
		else if(isAllLocs(t)){
			return OracleLocationSet.ALL_LOCS;
		}
		
		
		throw new RuntimeException("Unsupported locset operation: "+t.op());
	}
	
	
	
}
