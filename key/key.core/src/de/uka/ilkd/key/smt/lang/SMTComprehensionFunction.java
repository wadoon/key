package de.uka.ilkd.key.smt.lang;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.smt.SMTComprehensionTranslator.TermUtil;


public class SMTComprehensionFunction extends SMTFunction {
	private SMTFunction calcFunction;//function that is used to calculation
	private Term calcTerm; //calculation term
	private QuantifiableVariable qvar; //quantifiable variable of comprehension function
	private String type; //bsum, max,min
	
	
	
	public SMTComprehensionFunction(String id, List<SMTSort> domainSorts, SMTSort imageSort, SMTFunction calcFunction,Term calcTerm, QuantifiableVariable idxTerm, String type) {
		super(id,domainSorts,imageSort);
		this.calcFunction = calcFunction;
		this.calcTerm = calcTerm;
		this.qvar = idxTerm;
		this.type = type;
	    }

	

	public SMTFunction getCalcFunction() {
		return calcFunction;
	}
	
	

	public Term getCalcTerm() {
		return calcTerm;
	}

	public void setCalcTerm(Term calcTerm) {
		this.calcTerm = calcTerm;
	}

	public void setCalcFunction(SMTFunction calcFunction) {
		this.calcFunction = calcFunction;
	}
	
	
	
	



	public QuantifiableVariable getQvar() {
		return qvar;
	}



	public void setQvar(QuantifiableVariable qvar) {
		this.qvar = qvar;
	}



	public String getType() {
		return type;
	}

	public void setType(String type) {
		this.type = type;
	}

	public SMTComprehensionFunction searchIdentical(List<SMTComprehensionFunction> listCompreFuncs, Services services){
		for(SMTComprehensionFunction func: listCompreFuncs){
			if(identical(func, services))
				return func;			
		}
		return null;
	}
	
	
	 /*check if this comprehension function and qf are identical  */
    public boolean identical(SMTComprehensionFunction func, Services services){
       if(type.equals(func.getType())){
          /*
           * replace all idx in qf.calcExpr by this.idx and afterwards, compare qf.calcExpr and this.calcExpr 
           * */
          if(calcFunction.getDomainSorts().size() != func.getCalcFunction().getDomainSorts().size())
             return false;
          if(!calcFunction.getImageSort().equals(func.getCalcFunction().getImageSort()))
             return false;
          TermBuilder termBuilder = services.getTermBuilder();
          
          Term substCalcTerm = TermUtil.repalce(termBuilder.var(qvar), termBuilder.var(func.getQvar()), calcTerm, services);
          System.out.println("compare: \n"+substCalcTerm.toString() + "\n" + func.getCalcTerm().toString());
          if(substCalcTerm.toString().equals(func.getCalcTerm().toString())){               
             return true;
          }else{
             return false;
          }               
       }else            
          return false;
    }     
	
}
