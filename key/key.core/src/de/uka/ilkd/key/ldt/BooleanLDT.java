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

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.services.TermServices;
import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.util.Debug;


/** 
 * This class inherits from LDT and implements all method that are
 * necessary to handle the primitive type boolean.
 */
public final class BooleanLDT extends LDT {
    
    public static final Name NAME = new Name("boolean");
    
    /** the boolean literals as function symbols and terms */
    private final Function bool_true;
    private final JavaDLTerm term_bool_true;
    private final Function bool_false;
    private final JavaDLTerm term_bool_false;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------    

    public BooleanLDT(TermServices services) {
        super(NAME, services);
        
        bool_true       = addFunction(services, "TRUE");
	term_bool_true  = services.getTermBuilder().func(bool_true);
	bool_false      = addFunction(services, "FALSE");
	term_bool_false = services.getTermBuilder().func(bool_false);
    }
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public JavaDLTerm getFalseTerm() {
        return term_bool_false;
    }

    
    public JavaDLTerm getTrueTerm() {
        return term_bool_true;
    }

    
    /**
     * returns the function representing the boolean value <tt>FALSE</tt>
     */
    public Function getFalseConst() {
        return bool_false;
    }

    
    /**
     * returns the function representing the boolean value <tt>TRUE</tt>
     */
    public Function getTrueConst() {
        return bool_true;
    }

    
    @Override
    public boolean isResponsible
	(de.uka.ilkd.key.java.expression.Operator op, JavaDLTerm[] subs, 
                Services services, ExecutionContext ec) {
	if (subs.length == 1) {
	    return isResponsible(op, subs[0], services, ec);
	} else if (subs.length == 2) {
	    return isResponsible(op, subs[0], subs[1], services, ec);	
	}
	return false;	
    }

    
    @Override
    public boolean isResponsible
	(de.uka.ilkd.key.java.expression.Operator op, JavaDLTerm left, JavaDLTerm right, Services services, ExecutionContext ec) {
	return false;

    }

    
    @Override
    public boolean isResponsible
	(de.uka.ilkd.key.java.expression.Operator op, JavaDLTerm sub, TermServices services, ExecutionContext ec) {
	return false;
    }

    
    @Override 
    public JavaDLTerm translateLiteral(Literal lit, Services services) {
	if (lit instanceof BooleanLiteral) {
	    return (((BooleanLiteral)lit).getValue() ? 
		    term_bool_true : term_bool_false);
	}
	Debug.fail("booleanLDT: Wrong literal", lit);	
	return null;
    }

    
    @Override
    public Function getFunctionFor
	(de.uka.ilkd.key.java.expression.Operator op, Services services, 
                ExecutionContext ec) {
	assert false;
	return null;
    }   


    @Override
    public boolean hasLiteralFunction(Function f) {
	return containsFunction(f) && f.arity()==0;
    }

    
    @Override
    public Expression translateTerm(JavaDLTerm t, ExtList children, Services services) {
	if(t.op() == bool_true) {
	    return BooleanLiteral.TRUE;
	} else if(t.op() == bool_false) { 
	    return BooleanLiteral.FALSE;
	} else {
	    assert false : "BooleanLDT: Cannot convert term to program: " + t;
	    return null;
	}
    }
    
    
    @Override
    public final Type getType(JavaDLTerm t) {
	if(t.sort() == targetSort()) {
	    return PrimitiveType.JAVA_BOOLEAN;
	} else {
	    assert false : "BooleanLDT: Cannot get Java type for term: " + t;
	    return null;
	}
    }
}