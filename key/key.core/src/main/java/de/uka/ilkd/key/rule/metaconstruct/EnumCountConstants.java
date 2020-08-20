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

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.EnumClassDeclaration;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.conditions.EnumConstantCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * resolve a program variable to an integer literal.
 * 
 * If the PC is a term of an enum type, then the number
 * of enum constants in that type is returned.
 * 
 * @author mulbrich
 */
public final class EnumCountConstants extends AbstractTermTransformer {

    public EnumCountConstants() {
        super(new Name("#enumcountconstants"), 1);
    }

    /**
     * calculates the resulting term.
     * 
     * If the program variable is the nextToCreate-field resolve it to the
     * number of enum constants of the container. Otherwise result in the index
     * of the constant.
     * 
     * @throws IllegalArgumentException
     *             if the argument is not of enum type
     */
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        KeYJavaType kjt = services.getTypeConverter().getKeYJavaType(term.sub(0));
        int value = EnumClassDeclaration.getNumberOfConstants(kjt);

        final IntLiteral valueLiteral = KeYJavaASTFactory.intLiteral(value);
	    term = services.getTypeConverter().convertToLogicElement(
		    valueLiteral);

        return term;
    }

}