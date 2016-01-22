// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.ldt;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.EmptySeqLiteral;
import de.uka.ilkd.key.java.expression.operator.adt.SeqConcat;
import de.uka.ilkd.key.java.expression.operator.adt.SeqGet;
import de.uka.ilkd.key.java.expression.operator.adt.SeqIndexOf;
import de.uka.ilkd.key.java.expression.operator.adt.SeqLength;
import de.uka.ilkd.key.java.expression.operator.adt.SeqReverse;
import de.uka.ilkd.key.java.expression.operator.adt.SeqSingleton;
import de.uka.ilkd.key.java.expression.operator.adt.SeqSub;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;


public final class OrdLDT extends LDT {
    
    public static final Name NAME = new Name("Ord");

    //  public name constants
    //  copied from SeqLDT.java, not clear if need here
    //  public static final Name SEQGET_NAME = new Name("seqGet");

    //getters
    //   private final SortDependingFunction seqGet;
    //  private final Function seqLen;
    // private final Function seqIndexOf; 
    
    //the following fields cache the symbols from ord.key. 
    private final Function o_0;
    private final Function o_1;
    private final Function omega;
    private final Function ord_add;
    private final Function ord_times ;
    private final Function ord_exp;
    private final Function ord_max;
    private final Function onat;
    private final Function ord_less;
    private final Function ord_leq;
    private final Function ord_lim;
    private final Function ord_sup;


    //-------------------------------------------------------------------------
    // constructor for class OrdLDT
    //-------------------------------------------------------------------------
   
    // names in green have to be the same as in ord.key 
    public OrdLDT(TermServices services) {
	super(NAME, services);
        o_0           = addFunction(services, "o_0");
        o_1           = addFunction(services, "o_1");
        omega         = addFunction(services, "omega");
        ord_add       = addFunction(services, "oadd");
        ord_times     = addFunction(services, "otimes");
        ord_exp       = addFunction(services, "oexp");
        ord_max       = addFunction(services, "omax");
        ord_leq       = addFunction(services, "oleq");
        onat    	= addFunction(services, "onat");
        ord_less      = addFunction(services, "olt");
        ord_lim	      = addFunction(services, "lim");
        ord_sup	      = addFunction(services, "osup");

    }
    
    //-------------------------------------------------------------------------
    // public interface
    //-------------------------------------------------------------------------   


   public Function getZero() {
	  return o_0;   }

   public Function getOne() {
	  return o_1;   }

   public Function getOmega() {
	  return omega;   }

   public Function getAdd() {
	return ord_add;
    }    
    
   public Function getTimes() {
	return ord_times;
    }  

   public Function getExp() {
	return ord_exp;
    }  

   public Function getMax() {
	return ord_max;
    }  
 
   public Function getLeq() {
	return ord_leq;
    }  
 
   public Function getOnat() {
	return onat;
    }  

   public Function getLess() {
	return ord_less;
    }  

  public Function getLim() {
	return ord_lim;
    }  
 
  public Function getSup() {
	return ord_sup;
    }  


    //-------------------------------------------------------------------------
    // I did not understand what "isResponsible" is good for.
    // Supplied trivial overrides   (PHS)
    //-------------------------------------------------------------------------   

  
    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
                                 Term[] subs, 
                                 Services services, 
                                 ExecutionContext ec) {
	return isResponsible(op, (Term)null, services, ec);
    }
    

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
                		 Term left, 
                		 Term right, 
                		 Services services, 
                		 ExecutionContext ec) {
	return false;
    }

    
    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
	    			 Term sub, 
	    			 TermServices services, 
	    			 ExecutionContext ec) {
	// 	return op instanceof SeqSingleton
	//       || op instanceof SeqConcat
	//	       || op instanceof SeqSub
	//       || op instanceof SeqReverse
	//       || op instanceof SeqIndexOf
	//       || op instanceof SeqGet
	//       || op instanceof SeqLength;
	return true;
    }



    //-------------------------------------------------------------------------
    // The following overwrites are also a mistery to me.
    // Tried to pacify the compiler   (PHS)
    //-------------------------------------------------------------------------  
 


       @Override
    public Term translateLiteral(Literal lit, Services services) {
    // 	assert lit instanceof DefaultOrdLiteral;
    	return services.getTermBuilder().func(o_0);
       }
    

      @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, 
	    			   Services serv, 
	    			   ExecutionContext ec) {
	  /*	if(op instanceof SeqSingleton) {
	    return seqSingleton;
	} else if(op instanceof SeqConcat) {
	    return seqConcat;
	} else if(op instanceof SeqSub) {
	    return seqSub;
	} else if(op instanceof SeqReverse) {
	    return seqReverse;
	} else if(op instanceof SeqIndexOf) {
	    return seqIndexOf;
	} else if(op instanceof SeqGet){
	    return seqGet;
	} else if(op instanceof SeqLength){
	    return seqLen;
	    } */
	assert false;
	return null;
	}  

    
       @Override
    public boolean hasLiteralFunction(Function f) {
	   //	return f.equals(seqEmpty);
	   return true;
    }

    
    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
	//	if(t.op().equals(seqEmpty)) {
	//    return EmptySeqLiteral.INSTANCE;
	//}
	//assert false;
	return null;
	}  
    
    
    @Override
    public final Type getType(Term t) {
	assert false;
	return null;
    }


 }