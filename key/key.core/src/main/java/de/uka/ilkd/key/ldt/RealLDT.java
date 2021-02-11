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

import de.uka.ilkd.key.java.expression.literal.RealLiteral;
import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;

/**
 * Complete this class if you want to add support for the JML \real type.
 *
 * At the moment this class contains only stubs.
 * @author Daniel Bruns, Rosa Abbasi
 */
public final class RealLDT extends LDT {

  public static final Name NAME = new Name("real");
  public static final Name REALLIT_NAME = new Name("R");//TODO?

  private final Function realLit;
  private final Function rlt;
  private final Function rlgt;
  private final Function rge;
  private final Function rgt;

  private final Function rNeg;
  private final Function rAdd;
  private final Function rMul;
  private final Function rSub;
  private final Function rDiv;


  public RealLDT(TermServices services) {

    super(NAME, services);

    realLit = addFunction(services, REALLIT_NAME.toString());

    rlt = addFunction(services, "rlt");
    rlgt = addFunction(services, "rlgt");
    rge = addFunction(services, "rge");
    rgt = addFunction(services, "rgt");

    rNeg = addFunction(services, "rAdd");
    rAdd = addFunction(services, "rAdd");
    rSub = addFunction(services, "rSub");
    rMul = addFunction(services, "rMul");
    rDiv = addFunction(services, "rDiv");

  }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	    			 Term[] subs,
	    			 Services services,
	    			 ExecutionContext ec) {
	return false;
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
	return false;
    }


    @Override
    public Term translateLiteral(Literal lit, Services services) {
        assert lit instanceof RealLiteral : "Must be a \\real literal";
        RealLiteral rlit = (RealLiteral) lit;
        return services.getTermBuilder().rTerm(rlit.getValue());
    }


    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op,
	    			   Services services,
	    			   ExecutionContext ec) {
	assert false;
	return null;
    }


    @Override
    public boolean hasLiteralFunction(Function f) {
	return false;
    }


    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
	return null;
    }


    @Override
    public final Type getType(Term t) {
	if(t.sort() == targetSort()) {
	    return PrimitiveType.JAVA_REAL;
	} else {
	    return null;
	}
    }

  public Function getRealSymbol() {
    return realLit;
  }

  public Function getRlt() { return rlt; }
  public Function getRlgt() {
    return rlgt;
  }
  public Function getRgt() {
    return rgt;
  }
  public Function getRge() {
    return rge;
  }

  public Function getRNeg() {
    return rNeg;
  }
  public Function getRAdd() {
    return rAdd;
  }
  public Function getRSub() {
    return rSub;
  }
  public Function getrMul() {
    return rMul;
  }
  public Function getrDiv() {
    return rDiv;
  }
}