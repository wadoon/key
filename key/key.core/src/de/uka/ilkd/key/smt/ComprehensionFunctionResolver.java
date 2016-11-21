package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.smt.SMTComprehensionTranslator.TermUtil;

/**
 * this class resolves quantified functions: sum, max, min
 * with sum function: it can translate sum function to bsum function
 * with max, min function: it can find and return tuple:
       (lowerBound, upperBound, comparisionExpr)
 * so that it can be solved into Z3 formula
 * */
public class ComprehensionFunctionResolver {   
   private Term func;
   private Services services;
   TermBuilder termBuilder;
   
   private Term lowerVal, upperVal;
   private QuantifiableVariable qv;
   
   
   /**
    * @param func
    * @param services
    */
   public ComprehensionFunctionResolver(Term func, Services services) {
      super();
      this.func = func;
      System.out.println("detected comprehension function: " + func);
      this.services = services;
      termBuilder=services.getTermBuilder();
      qv=this.func.boundVars().get(0); //assume that there is only one quantifiable variable
      lowerVal = null;
      upperVal = null; 
      travelFunction(func);
   }
   
   
   
    
    
    /*return quantifiable variable of function*/
    public QuantifiableVariable getQuantifiableVariable(){
       return qv;
    }
  
    public Term getLowerVal() {
      return lowerVal;
   }

   public Term getUpperVal() {
      return upperVal;
   }

   public Term getCalcTerm(){
      return func.sub(1);
   }
   /*
     * travel over t to detect lowerVal and upperVal
     * */
    private void travelFunction(Term t){       
       int x = checkLowerValTerm(t);
       if(x>=0){// means that t is lower term
          if(x==0){//lt(x,qv) ->lowerBound = x+1
             lowerVal = termBuilder.add(termBuilder.zTerm(1),t.sub(0));
          }else if(x==1){//le(x,qv) ->lowerBound = x
             lowerVal = t.sub(0);
          }else if(x==2){//gt(qv,x) -> lowerBound = x+1
             lowerVal = termBuilder.add(termBuilder.zTerm(1),t.sub(1));
          }else{//ge(qv,x) -> ->lowerBound = x
             lowerVal = t.sub(1);
          }          
       }else{
          x = checkUpperValTerm(t);
          if(x>=0){//means that t is upper term
             if(x==0){//lt(qv,x) ->upperBound = x
                upperVal = t.sub(1);
             }else if(x==1){ //le(qv,x) ->upperBound = x+1
                upperVal = termBuilder.add(termBuilder.zTerm(1), t.sub(1));
             }else if(x==2){//gt(x,qv) -> upperBound = x
                upperVal = t.sub(0);
             }else{//ge(x,qv) -> upperBound = x+1
                upperVal = termBuilder.add(termBuilder.zTerm(1),t.sub(0));
             }       
          }else if(t.subs().size()>0){
             //recursively find in t, using deep first search
             for(Term st: t.subs())
                travelFunction(st);
           }
       }          
    }
    
    /*
     * check if term t is lower value term
     * if t has the form lt(x,qv) ->0,lowerBound = x+1, or le(x,qv) ->1,lowerBound = x
     * if t has the form gt(qv,x) ->2,lowerBound = x+1 or ge(qv,x) ->3,lowerBound = x
     * otherwise return -1;
     * */
    private int checkLowerValTerm(Term t){
       if(TermUtil.isLessThan(t, services)||TermUtil.isLessOrEquals(t, services)){
          if(t.sub(1).toString().equals(qv.name().toString())){
             if(TermUtil.isLessThan(t, services)) //lt(x,qv) ->lowerBound = x+1
                return 0;
             else if(TermUtil.isLessOrEquals(t, services)) //le(x,qv) ->lowerBound = x
                return 1;
          }             
       }else if(TermUtil.isGreaterThan(t, services)||TermUtil.isGreaterOrEquals(t, services)){
          if(t.sub(0).toString().equals(qv.name().toString())){
             if(TermUtil.isGreaterThan(t, services)) //gt(qv,x) -> lowerBound = x+1
                return 2;
             else if(TermUtil.isGreaterOrEquals(t, services)) //ge(qv,x) -> ->lowerBound = x
                return 3;
          }
       }
       return -1;
    }
    
    /*
     * check if term t is upper value term and return the index of upper bound term
     * if t has the form lt(qv,x) ->upperBound = x-1 or le(qv,x) -> upperBound = x
     * if t has the form gt(x,qv) -> upperBound = x-1 or ge(x,qv) -> upperBound = x
     * otherwise return -1;
     * */
    private int checkUpperValTerm(Term t){
       if(TermUtil.isLessThan(t, services)||TermUtil.isLessOrEquals(t, services)){
          if(t.sub(0).toString().equals(qv.name().toString())){
             if(TermUtil.isLessThan(t, services)) //lt(qv,x) ->upperBound = x
                return 0;
             else if(TermUtil.isLessOrEquals(t, services)) //le(qv,x) ->upperBound = x+1
                return 1;
          }             
       }else if(TermUtil.isGreaterThan(t, services)||TermUtil.isGreaterOrEquals(t, services)){
          if(t.sub(1).toString().equals(qv.name().toString())){
             if(TermUtil.isGreaterThan(t, services)) //gt(x,qv) -> upperBound = x
                return 2;
             else if(TermUtil.isGreaterOrEquals(t, services)) //ge(x,qv) -> upperBound = x+1
                return 3;
          }
       }
       return -1;
    }
}