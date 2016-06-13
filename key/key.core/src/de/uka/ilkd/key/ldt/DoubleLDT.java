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
import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaDLTermServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JavaDLTerm;

/**
 * Complete this class if you want to add support for the Java double type.
 *
 * At the moment this class contains only stubs.
 */
public final class DoubleLDT extends LDT {

    public static final Name NAME = new Name("double");


    public DoubleLDT(JavaDLTermServices services) {
	super(NAME, services);
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	    			 JavaDLTerm[] subs,
	    			 Services services,
	    			 ExecutionContext ec) {
	return false;
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	    		         JavaDLTerm left,
	    		         JavaDLTerm right,
	    		         Services services,
	    		         ExecutionContext ec) {
	return false;
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	    		         JavaDLTerm sub,
	    		         JavaDLTermServices services,
	    		         ExecutionContext ec) {
	return false;
    }


    @Override
    public JavaDLTerm translateLiteral(Literal lit, Services services) {
        // return skolem term
        final Function sk = new Function(new Name(""+NAME+lit),targetSort());
        return services.getTermBuilder().func(sk);
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
    public Expression translateTerm(JavaDLTerm t, ExtList children, Services services) {
	return null;
    }


    @Override
    public final Type getType(JavaDLTerm t) {
	if(t.sort() == targetSort()) {
	    return PrimitiveType.JAVA_DOUBLE;
	} else {
	    return null;
	}
    }
}