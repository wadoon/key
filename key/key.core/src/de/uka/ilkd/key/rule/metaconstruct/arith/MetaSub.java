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

package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import org.key_project.common.core.logic.Name;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public class MetaSub extends AbstractTermTransformer {

    public MetaSub() {
	super(new Name("#sub"), 2);
    }


    public JavaDLTerm transform(JavaDLTerm term, SVInstantiations svInst, Services services) {
	JavaDLTerm arg1 = term.sub(0);
	JavaDLTerm arg2 = term.sub(1);
	BigInteger bigIntArg1;
	BigInteger bigIntArg2;

	bigIntArg1 = new
	    BigInteger(convertToDecimalString(arg1, services));
	bigIntArg2 = new
	    BigInteger(convertToDecimalString(arg2, services));

	BigInteger bigIntResult = bigIntArg1.subtract(bigIntArg2);
	
	IntLiteral lit = new IntLiteral(bigIntResult.toString());
	return services.getProgramServices().getTypeConverter().convertToLogicElement(lit);
    }
}