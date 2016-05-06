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
import de.uka.ilkd.key.java.expression.literal.OrdOneLiteral;
import de.uka.ilkd.key.java.expression.literal.OrdZeroLiteral;
import de.uka.ilkd.key.java.expression.literal.OrdOmegaLiteral;
import de.uka.ilkd.key.java.expression.operator.adt.OrdOnat;
import de.uka.ilkd.key.java.expression.operator.adt.OrdAdd;
import de.uka.ilkd.key.java.expression.operator.adt.OrdExp;
import de.uka.ilkd.key.java.expression.operator.adt.OrdMax;
import de.uka.ilkd.key.java.expression.operator.adt.OrdTimes;
import de.uka.ilkd.key.java.expression.operator.adt.OrdLess;
import de.uka.ilkd.key.java.expression.operator.adt.OrdLeq;
import de.uka.ilkd.key.java.expression.operator.adt.OrdLim;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;


public final class OrdLDT extends LDT {
    
    public static final Name NAME = new Name("Ord");
 
     //getters
 
     private final Function ordLess;
    private final Function ordLeq;
    private final Function ordLim;
  
    // constructors
    private final Function ord0;
    private final Function ord1;
    private final Function omega;
    private final Function ordAdd;
    private final Function ordTimes ;
    private final Function ordExp;
    private final Function ordMax;
    private final Function onat;
    private final Function ordSup;
   
 
    public OrdLDT(TermServices services) {
	super(NAME, services);
        ord0           = addFunction(services, "o_0");
        ord1           = addFunction(services, "o_1");
        omega          = addFunction(services, "omega");
        ordAdd         = addFunction(services, "oadd");
        ordTimes       = addFunction(services, "otimes");
        ordExp         = addFunction(services, "oexp");
        ordMax         = addFunction(services, "omax");
        ordLeq         = addFunction(services, "oleq");
        onat           = addFunction(services, "onat");
        ordLess        = addFunction(services, "olt");
        ordLim	       = addFunction(services, "lim");
        ordSup	       = addFunction(services, "osup");

    }
    
    //-------------------------------------------------------------------------
    // public interface
    //-------------------------------------------------------------------------   



   public Function getOrd0() {
	  return ord0;   }

   public Function getOrd1() {
	  return ord1;   }

   public Function getOmega() {
	  return omega;   }

   public Function getOrdAdd() {
	return ordAdd;
    }    
    
   public Function getOrdTimes() {
	return ordTimes;
    }  

   public Function getOrdExp() {
	return ordExp;
    }  

   public Function getOrdMax() {
	return ordMax;
    }  
 
   public Function getOrdLeq() {
	return ordLeq;
    }  
 
   public Function getOnat() {
	return onat;
    }  

   public Function getOrdLess() {
	return ordLess;
    }  

  public Function getOrdLim() {
	return ordLim;
    }  
 
  public Function getOrdSup() {
	return ordSup;
    }  


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
	 	return 
		 (op instanceof OrdOnat
	       || op instanceof OrdExp
	       || op instanceof OrdAdd
	       || op instanceof OrdMax
	       || op instanceof OrdTimes
	       || op instanceof OrdLess
	       || op instanceof OrdLeq
	       || op instanceof OrdLim);
               }

        @Override
    public Term translateLiteral(Literal lit, Services services) {
     	assert (    lit instanceof OrdOneLiteral
                ||  lit instanceof OrdZeroLiteral
		||  lit instanceof OrdOmegaLiteral);

	if(lit instanceof OrdOneLiteral) {
	    return services.getTermBuilder().func(ord1);
	}  else if(lit instanceof OrdZeroLiteral) {
	    return services.getTermBuilder().func(ord0);
	}  else if(lit instanceof OrdOmegaLiteral) {
	    return services.getTermBuilder().func(omega);
	}
	assert false;
	return null;
       }
  
      @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, 
	    			   Services serv, 
	    			   ExecutionContext ec) {
	   if(op instanceof OrdOnat) {
	    return onat;
        }  else if(op instanceof OrdAdd) {
	    return ordAdd;
	} else if(op instanceof OrdExp) {
	    return ordExp;
	} else if(op instanceof OrdMax) {
	    return ordMax;
	} else if(op instanceof OrdTimes) {
	    return ordTimes;
	} else if(op instanceof OrdLess){
	    return ordLess;
	} else if(op instanceof OrdLeq){
	    return ordLeq;
	} else if(op instanceof OrdLim){
	    return ordLim;
	    } 
	assert false;
	return null;
	}  

  //-------------------------------------------------------------------------
    // The following overwrite is still  a mistery to me.
    // Tried to pacify the compiler   (PHS)
    //-------------------------------------------------------------------------  
    
       @Override
    public boolean hasLiteralFunction(Function f) {
	   //	return f.equals(seqEmpty);
	   return true;
    }

    
    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
       if(t.op().equals(ord0)) {
	   return OrdZeroLiteral.INSTANCE;
       } else if(t.op().equals(ord1)) {
          return OrdOneLiteral.INSTANCE;
       } else if(t.op().equals(omega)) {
          return OrdOmegaLiteral.INSTANCE;
       }
	assert false;
	return null;
    } 

    @Override
    public final Type getType(Term t) {
	assert false;
	return null;
    }


 }